#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
电子书分类整理工具
扫描指定文件夹中的EPUB、PDF、MOBI文件，按语言和类别自动分类整理。
"""

import os
import sys
import json
import shutil
import argparse
import zipfile
import re
import hashlib
from pathlib import Path
from collections import defaultdict
from datetime import datetime

try:
    from PyPDF2 import PdfReader
    HAS_PYPDF2 = True
except ImportError:
    HAS_PYPDF2 = False

try:
    from PIL import Image
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

try:
    import ebooklib
    from ebooklib import epub
    HAS_EBOOKLIB = True
except ImportError:
    HAS_EBOOKLIB = False


SUPPORTED_EXTENSIONS = {'.epub', '.pdf', '.mobi'}


class BookMetadata:
    """电子书元数据"""
    def __init__(self):
        self.title = ''
        self.author = ''
        self.language = ''
        self.publisher = ''
        self.pub_date = ''
        self.description = ''
        self.cover_image = None  # bytes
        self.cover_ext = '.jpg'
        self.file_path = ''
        self.file_size = 0
        self.file_type = ''
        self.detected_language = ''
        self.language_confidence = 0
        self.category = ''
        self.target_path = ''


def detect_language_by_chars(text):
    """通过字符特征检测语言"""
    if not text:
        return ('unknown', 0)

    zh_count = 0
    ja_hiragana = 0
    ja_katakana = 0
    ko_count = 0
    en_count = 0
    total_chars = 0

    for ch in text:
        code = ord(ch)
        if '\u4e00' <= ch <= '\u9fff' or '\u3400' <= ch <= '\u4dbf':
            zh_count += 1
            total_chars += 1
        elif '\u3040' <= ch <= '\u309f':
            ja_hiragana += 1
            total_chars += 1
        elif '\u30a0' <= ch <= '\u30ff':
            ja_katakana += 1
            total_chars += 1
        elif '\uac00' <= ch <= '\ud7af' or '\u1100' <= ch <= '\u11ff':
            ko_count += 1
            total_chars += 1
        elif ch.isalpha() and ch.isascii():
            en_count += 1
            total_chars += 1

    if total_chars == 0:
        return ('unknown', 0)

    ja_total = ja_hiragana + ja_katakana

    zh_ratio = zh_count / total_chars
    ja_ratio = ja_total / total_chars
    ko_ratio = ko_count / total_chars
    en_ratio = en_count / total_chars

    if zh_ratio > 0.3 and ja_ratio < 0.05:
        return ('zh', zh_ratio)
    elif ja_ratio > 0.1 or (ja_hiragana > 5 or ja_katakana > 5):
        return ('ja', max(ja_ratio, 0.3))
    elif ko_ratio > 0.1:
        return ('ko', ko_ratio)
    elif en_ratio > 0.5:
        return ('en', en_ratio)
    elif zh_ratio > 0.1:
        return ('zh', zh_ratio)
    else:
        return ('unknown', 0)


def detect_language_by_filename(filename):
    """通过文件名猜测语言"""
    name = Path(filename).stem
    lang, conf = detect_language_by_chars(name)
    return (lang, conf)


def read_epub_metadata(filepath):
    """读取EPUB元数据"""
    meta = BookMetadata()
    meta.file_path = filepath
    meta.file_size = os.path.getsize(filepath)
    meta.file_type = 'epub'

    try:
        if HAS_EBOOKLIB:
            book = epub.read_epub(filepath)
            titles = book.get_metadata('DC', 'title')
            if titles:
                meta.title = titles[0][0]

            creators = book.get_metadata('DC', 'creator')
            if creators:
                meta.author = creators[0][0]

            langs = book.get_metadata('DC', 'language')
            if langs:
                lang_code = langs[0][0].lower()
                if lang_code.startswith('zh'):
                    meta.language = 'zh'
                elif lang_code.startswith('en'):
                    meta.language = 'en'
                elif lang_code.startswith('ja'):
                    meta.language = 'ja'
                elif lang_code.startswith('ko'):
                    meta.language = 'ko'
                else:
                    meta.language = lang_code.split('-')[0]

            publishers = book.get_metadata('DC', 'publisher')
            if publishers:
                meta.publisher = publishers[0][0]

            dates = book.get_metadata('DC', 'date')
            if dates:
                meta.pub_date = dates[0][0]

            descriptions = book.get_metadata('DC', 'description')
            if descriptions:
                meta.description = descriptions[0][0]

            for item in book.get_items():
                if item.get_type() == ebooklib.ITEM_COVER:
                    meta.cover_image = item.get_content()
                    name = item.get_name().lower()
                    if name.endswith('.png'):
                        meta.cover_ext = '.png'
                    elif name.endswith('.gif'):
                        meta.cover_ext = '.gif'
                    break

            if meta.cover_image is None:
                for item in book.get_items():
                    if hasattr(item, 'get_name'):
                        name = item.get_name().lower()
                        if 'cover' in name and (name.endswith('.jpg') or name.endswith('.jpeg') or name.endswith('.png')):
                            meta.cover_image = item.get_content()
                            if name.endswith('.png'):
                                meta.cover_ext = '.png'
                            break
        else:
            with zipfile.ZipFile(filepath, 'r') as zf:
                opf_path = None
                for name in zf.namelist():
                    if name.lower().endswith('.opf'):
                        opf_path = name
                        break

                if opf_path:
                    content = zf.read(opf_path).decode('utf-8', errors='ignore')
                    title_match = re.search(r'<dc:title[^>]*>(.*?)</dc:title>', content, re.IGNORECASE | re.DOTALL)
                    if title_match:
                        meta.title = title_match.group(1).strip()

                    creator_match = re.search(r'<dc:creator[^>]*>(.*?)</dc:creator>', content, re.IGNORECASE | re.DOTALL)
                    if creator_match:
                        meta.author = creator_match.group(1).strip()

                    lang_match = re.search(r'<dc:language[^>]*>(.*?)</dc:language>', content, re.IGNORECASE | re.DOTALL)
                    if lang_match:
                        lang_code = lang_match.group(1).strip().lower()
                        if lang_code.startswith('zh'):
                            meta.language = 'zh'
                        elif lang_code.startswith('en'):
                            meta.language = 'en'
                        elif lang_code.startswith('ja'):
                            meta.language = 'ja'
                        else:
                            meta.language = lang_code.split('-')[0]

                    cover_match = re.search(r'<meta[^>]*name="cover"[^>]*content="([^"]+)"', content, re.IGNORECASE)
                    if cover_match:
                        cover_id = cover_match.group(1)
                        href_match = re.search(
                            r'<item[^>]*id="' + re.escape(cover_id) + r'"[^>]*href="([^"]+)"',
                            content, re.IGNORECASE
                        )
                        if href_match:
                            cover_href = href_match.group(1)
                            opf_dir = os.path.dirname(opf_path)
                            cover_path = os.path.join(opf_dir, cover_href) if opf_dir else cover_href
                            cover_path = cover_path.replace('\\', '/')
                            try:
                                cover_data = zf.read(cover_path)
                                meta.cover_image = cover_data
                                if cover_path.lower().endswith('.png'):
                                    meta.cover_ext = '.png'
                            except KeyError:
                                pass

                if meta.cover_image is None:
                    for name in zf.namelist():
                        lower_name = name.lower()
                        if 'cover' in lower_name and (lower_name.endswith('.jpg') or lower_name.endswith('.jpeg') or lower_name.endswith('.png')):
                            try:
                                meta.cover_image = zf.read(name)
                                if lower_name.endswith('.png'):
                                    meta.cover_ext = '.png'
                                break
                            except KeyError:
                                pass
    except Exception as e:
        print(f"读取EPUB元数据出错 {filepath}: {e}")

    return meta


def read_pdf_metadata(filepath):
    """读取PDF元数据"""
    meta = BookMetadata()
    meta.file_path = filepath
    meta.file_size = os.path.getsize(filepath)
    meta.file_type = 'pdf'

    try:
        if HAS_PYPDF2:
            reader = PdfReader(filepath)
            info = reader.metadata
            if info:
                if info.title:
                    meta.title = str(info.title)
                if info.author:
                    meta.author = str(info.author)
                if info.subject:
                    meta.description = str(info.subject)
                if info.publisher:
                    meta.publisher = str(info.publisher)

            try:
                page = reader.pages[0]
                if '/Lang' in page:
                    lang = str(page['/Lang']).lower()
                    if lang.startswith('zh'):
                        meta.language = 'zh'
                    elif lang.startswith('en'):
                        meta.language = 'en'
                    elif lang.startswith('ja'):
                        meta.language = 'ja'
                    else:
                        meta.language = lang.split('-')[0]
            except Exception:
                pass

            try:
                if len(reader.pages) > 0:
                    first_page = reader.pages[0]
                    text = first_page.extract_text() or ''
                    if not meta.language:
                        lang, conf = detect_language_by_chars(text[:2000])
                        if lang != 'unknown':
                            meta.language = lang
            except Exception:
                pass
    except Exception as e:
        print(f"读取PDF元数据出错 {filepath}: {e}")

    return meta


def read_mobi_metadata(filepath):
    """读取MOBI元数据（基础解析）"""
    meta = BookMetadata()
    meta.file_path = filepath
    meta.file_size = os.path.getsize(filepath)
    meta.file_type = 'mobi'

    try:
        with open(filepath, 'rb') as f:
            data = f.read(4096)

            if data[60:64] == b'BOOK':
                title_offset = int.from_bytes(data[84:88], 'big')
                title_length = int.from_bytes(data[88:92], 'big')
                if title_offset + title_length <= len(data):
                    meta.title = data[title_offset:title_offset + title_length].decode('utf-8', errors='ignore').strip('\x00')

                author_offset = int.from_bytes(data[92:96], 'big')
                author_length = int.from_bytes(data[96:100], 'big')
                if author_offset + author_length <= len(data):
                    meta.author = data[author_offset:author_offset + author_length].decode('utf-8', errors='ignore').strip('\x00')

                lang_offset = int.from_bytes(data[100:104], 'big')
                lang_length = int.from_bytes(data[104:108], 'big')
                if lang_offset + lang_length <= len(data):
                    lang_code = data[lang_offset:lang_offset + lang_length].decode('utf-8', errors='ignore').strip('\x00').lower()
                    if lang_code.startswith('zh'):
                        meta.language = 'zh'
                    elif lang_code.startswith('en'):
                        meta.language = 'en'
                    elif lang_code.startswith('ja'):
                        meta.language = 'ja'
                    else:
                        meta.language = lang_code.split('-')[0] if lang_code else ''
    except Exception as e:
        print(f"读取MOBI元数据出错 {filepath}: {e}")

    return meta


def get_book_text_preview(filepath, file_type, max_chars=2000):
    """获取书籍文本预览用于语言检测"""
    try:
        if file_type == 'epub':
            with zipfile.ZipFile(filepath, 'r') as zf:
                text = ''
                for name in sorted(zf.namelist()):
                    if name.lower().endswith(('.html', '.htm', '.xhtml')):
                        try:
                            content = zf.read(name).decode('utf-8', errors='ignore')
                            content = re.sub(r'<[^>]+>', ' ', content)
                            content = re.sub(r'\s+', ' ', content).strip()
                            text += content
                            if len(text) > max_chars * 2:
                                break
                        except Exception:
                            continue
                return text[:max_chars]

        elif file_type == 'pdf' and HAS_PYPDF2:
            reader = PdfReader(filepath)
            text = ''
            for i, page in enumerate(reader.pages):
                if i > 10:
                    break
                try:
                    page_text = page.extract_text() or ''
                    text += page_text
                    if len(text) > max_chars * 2:
                        break
                except Exception:
                    continue
            return text[:max_chars]
    except Exception:
        pass
    return ''


def detect_book_language(meta, text_detection_chars=2000):
    """综合判断书籍语言"""
    lang_confidences = []

    if meta.language:
        lang_confidences.append((meta.language, 0.9))

    filename_lang, filename_conf = detect_language_by_filename(os.path.basename(meta.file_path))
    if filename_lang != 'unknown':
        lang_confidences.append((filename_lang, filename_conf * 0.5))

    if meta.title:
        title_lang, title_conf = detect_language_by_chars(meta.title)
        if title_lang != 'unknown':
            lang_confidences.append((title_lang, title_conf * 0.7))

    if meta.description:
        desc_lang, desc_conf = detect_language_by_chars(meta.description)
        if desc_lang != 'unknown':
            lang_confidences.append((desc_lang, desc_conf * 0.8))

    text_lang = None
    text_conf = 0
    if not any(lang in {'zh', 'en', 'ja', 'ko'} for lang, _ in lang_confidences) or not lang_confidences:
        text = get_book_text_preview(meta.file_path, meta.file_type, text_detection_chars)
        if text:
            text_lang, text_conf = detect_language_by_chars(text)
            if text_lang != 'unknown':
                lang_confidences.append((text_lang, text_conf * 0.9))

    if not lang_confidences:
        return ('unknown', 0)

    lang_scores = defaultdict(float)
    for lang, conf in lang_confidences:
        lang_scores[lang] += conf

    best_lang = max(lang_scores, key=lang_scores.get)
    return (best_lang, lang_scores[best_lang])


def classify_book(meta, rules):
    """根据规则对书籍进行子分类"""
    lang = meta.detected_language
    if lang not in rules.get('subcategories', {}):
        return rules.get('default_category', '其他')

    subcategories = rules['subcategories'][lang]
    default_cat = rules.get('default_category', '其他')

    search_text = f"{meta.title} {meta.description}"

    category_scores = {}
    for cat_name, cat_info in sorted(subcategories.items(), key=lambda x: x[1].get('priority', 99)):
        keywords = cat_info.get('keywords', [])
        score = 0
        for keyword in keywords:
            count = search_text.lower().count(keyword.lower())
            if count > 0:
                score += count * (1 / cat_info.get('priority', 1))
        if score > 0:
            category_scores[cat_name] = score

    if category_scores:
        return max(category_scores, key=category_scores.get)

    return default_cat


def scan_books(folder):
    """扫描文件夹中的电子书"""
    books = []
    for root, dirs, files in os.walk(folder):
        for filename in files:
            ext = os.path.splitext(filename)[1].lower()
            if ext in SUPPORTED_EXTENSIONS:
                filepath = os.path.join(root, filename)
                books.append((filepath, ext[1:]))
    return books


def read_metadata(filepath, file_type):
    """读取电子书元数据"""
    if file_type == 'epub':
        return read_epub_metadata(filepath)
    elif file_type == 'pdf':
        return read_pdf_metadata(filepath)
    elif file_type == 'mobi':
        return read_mobi_metadata(filepath)
    else:
        meta = BookMetadata()
        meta.file_path = filepath
        meta.file_size = os.path.getsize(filepath)
        meta.file_type = file_type
        return meta


def format_size(size_bytes):
    """格式化文件大小"""
    if size_bytes < 1024:
        return f"{size_bytes} B"
    elif size_bytes < 1024 * 1024:
        return f"{size_bytes / 1024:.2f} KB"
    elif size_bytes < 1024 * 1024 * 1024:
        return f"{size_bytes / (1024 * 1024):.2f} MB"
    else:
        return f"{size_bytes / (1024 * 1024 * 1024):.2f} GB"


def generate_statistics(books, rules):
    """生成统计报表"""
    lang_stats = defaultdict(lambda: {'count': 0, 'size': 0, 'categories': defaultdict(lambda: {'count': 0, 'size': 0})})
    unprocessed = []

    for meta in books:
        lang = meta.detected_language
        lang_stats[lang]['count'] += 1
        lang_stats[lang]['size'] += meta.file_size
        if meta.category:
            lang_stats[lang]['categories'][meta.category]['count'] += 1
            lang_stats[lang]['categories'][meta.category]['size'] += meta.file_size
        if lang == 'unknown':
            unprocessed.append(meta)

    return lang_stats, unprocessed


def print_statistics(lang_stats, rules, unprocessed):
    """打印统计报表"""
    lang_folders = rules.get('language_folders', {})

    print("\n" + "=" * 60)
    print("电子书分类统计报表")
    print("=" * 60)

    total_count = sum(v['count'] for v in lang_stats.values())
    total_size = sum(v['size'] for v in lang_stats.values())

    print(f"\n总计: {total_count} 本书, 总大小: {format_size(total_size)}")
    print("-" * 60)

    for lang in sorted(lang_stats.keys(), key=lambda x: lang_stats[x]['count'], reverse=True):
        stats = lang_stats[lang]
        lang_name = lang_folders.get(lang, lang)
        percentage = (stats['count'] / total_count * 100) if total_count > 0 else 0
        print(f"\n【{lang_name}】 {stats['count']} 本 ({percentage:.1f}%), 大小: {format_size(stats['size'])}")

        if stats['categories']:
            for cat in sorted(stats['categories'].keys(), key=lambda x: stats['categories'][x]['count'], reverse=True):
                cat_stats = stats['categories'][cat]
                cat_pct = (cat_stats['count'] / stats['count'] * 100) if stats['count'] > 0 else 0
                print(f"  └─ {cat}: {cat_stats['count']} 本 ({cat_pct:.1f}%), {format_size(cat_stats['size'])}")

    if unprocessed:
        print(f"\n{'=' * 60}")
        print(f"无法识别语言的文件 ({len(unprocessed)} 个):")
        print("-" * 60)
        for meta in unprocessed:
            print(f"  - {os.path.basename(meta.file_path)} ({format_size(meta.file_size)})")

    print("\n" + "=" * 60)


def save_thumbnail(meta, output_dir, size=(120, 160)):
    """保存封面缩略图"""
    if not meta.cover_image or not HAS_PIL:
        return None

    try:
        os.makedirs(output_dir, exist_ok=True)

        file_hash = hashlib.md5(meta.file_path.encode()).hexdigest()[:8]
        thumb_filename = f"thumb_{file_hash}{meta.cover_ext}"
        thumb_path = os.path.join(output_dir, thumb_filename)

        if os.path.exists(thumb_path):
            return thumb_filename

        from io import BytesIO
        img = Image.open(BytesIO(meta.cover_image))
        img.thumbnail(size, Image.LANCZOS)

        if img.mode in ('RGBA', 'P') and meta.cover_ext in ('.jpg', '.jpeg'):
            background = Image.new('RGB', img.size, (255, 255, 255))
            if img.mode == 'P':
                img = img.convert('RGBA')
            background.paste(img, mask=img.split()[-1] if img.mode == 'RGBA' else None)
            background.save(thumb_path, 'JPEG', quality=85)
        else:
            img.save(thumb_path)

        return thumb_filename
    except Exception as e:
        print(f"生成缩略图失败 {meta.file_path}: {e}")
        return None


def generate_html_index(books, rules, output_dir):
    """生成HTML索引页"""
    lang_folders = rules.get('language_folders', {})
    thumbs_dir = os.path.join(output_dir, 'thumbs')
    os.makedirs(thumbs_dir, exist_ok=True)

    print("\n正在生成封面缩略图...")
    for meta in books:
        thumb_name = save_thumbnail(meta, thumbs_dir)
        meta.thumb_filename = thumb_name

    books_by_lang = defaultdict(list)
    for meta in books:
        books_by_lang[meta.detected_language].append(meta)

    html = '''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>电子书索引</title>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body {
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', 'Microsoft YaHei', sans-serif;
    background: #f5f5f5;
    color: #333;
    padding: 20px;
}
.container { max-width: 1400px; margin: 0 auto; }
h1 {
    text-align: center;
    margin-bottom: 30px;
    color: #2c3e50;
    font-size: 2em;
}
.stats-bar {
    background: white;
    padding: 20px;
    border-radius: 10px;
    margin-bottom: 30px;
    display: flex;
    justify-content: space-around;
    flex-wrap: wrap;
    box-shadow: 0 2px 10px rgba(0,0,0,0.1);
}
.stat-item { text-align: center; padding: 10px; }
.stat-value { font-size: 1.8em; font-weight: bold; color: #3498db; }
.stat-label { color: #7f8c8d; margin-top: 5px; }
.language-section { margin-bottom: 40px; }
.lang-title {
    font-size: 1.5em;
    color: #2c3e50;
    margin-bottom: 20px;
    padding-bottom: 10px;
    border-bottom: 3px solid #3498db;
    display: inline-block;
}
.book-grid {
    display: grid;
    grid-template-columns: repeat(auto-fill, minmax(200px, 1fr));
    gap: 20px;
}
.book-card {
    background: white;
    border-radius: 10px;
    padding: 15px;
    box-shadow: 0 2px 8px rgba(0,0,0,0.1);
    transition: transform 0.2s, box-shadow 0.2s;
    display: flex;
    flex-direction: column;
}
.book-card:hover {
    transform: translateY(-5px);
    box-shadow: 0 5px 20px rgba(0,0,0,0.15);
}
.book-cover {
    width: 100%;
    height: 180px;
    object-fit: contain;
    background: #f0f0f0;
    border-radius: 5px;
    margin-bottom: 10px;
}
.no-cover {
    display: flex;
    align-items: center;
    justify-content: center;
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    color: white;
    font-size: 0.9em;
    text-align: center;
    padding: 10px;
}
.book-title {
    font-weight: bold;
    font-size: 0.95em;
    margin-bottom: 5px;
    display: -webkit-box;
    -webkit-line-clamp: 2;
    -webkit-box-orient: vertical;
    overflow: hidden;
    min-height: 2.4em;
}
.book-author {
    color: #7f8c8d;
    font-size: 0.85em;
    margin-bottom: 8px;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}
.book-meta {
    margin-top: auto;
    display: flex;
    justify-content: space-between;
    font-size: 0.8em;
    color: #95a5a6;
}
.badge {
    display: inline-block;
    padding: 2px 8px;
    border-radius: 10px;
    font-size: 0.75em;
    background: #ecf0f1;
    color: #7f8c8d;
}
.badge-lang-zh { background: #e8f5e9; color: #2e7d32; }
.badge-lang-en { background: #e3f2fd; color: #1565c0; }
.badge-lang-ja { background: #fff3e0; color: #e65100; }
.badge-lang-unknown { background: #ffebee; color: #c62828; }
.category-title {
    font-size: 1.1em;
    color: #34495e;
    margin: 20px 0 15px 0;
    padding-left: 10px;
    border-left: 4px solid #3498db;
}
footer {
    text-align: center;
    margin-top: 50px;
    padding: 20px;
    color: #95a5a6;
    font-size: 0.9em;
}
.nav-tabs {
    display: flex;
    gap: 10px;
    margin-bottom: 20px;
    flex-wrap: wrap;
}
.nav-tab {
    padding: 10px 20px;
    background: white;
    border: none;
    border-radius: 20px;
    cursor: pointer;
    font-size: 0.95em;
    box-shadow: 0 2px 5px rgba(0,0,0,0.1);
    transition: all 0.2s;
}
.nav-tab:hover { background: #3498db; color: white; }
.nav-tab.active { background: #3498db; color: white; }
</style>
</head>
<body>
<div class="container">
<h1>📚 电子书索引库</h1>
'''

    total_count = len(books)
    total_size = sum(m.file_size for m in books)
    lang_count = len(books_by_lang)

    html += f'''
<div class="stats-bar">
    <div class="stat-item">
        <div class="stat-value">{total_count}</div>
        <div class="stat-label">书籍总数</div>
    </div>
    <div class="stat-item">
        <div class="stat-value">{format_size(total_size)}</div>
        <div class="stat-label">总大小</div>
    </div>
    <div class="stat-item">
        <div class="stat-value">{lang_count}</div>
        <div class="stat-label">语言种类</div>
    </div>
    <div class="stat-item">
        <div class="stat-value">{datetime.now().strftime('%Y-%m-%d')}</div>
        <div class="stat-label">生成日期</div>
    </div>
</div>
'''

    html += '<div class="nav-tabs">'
    for i, (lang, lang_books) in enumerate(sorted(books_by_lang.items(), key=lambda x: len(x[1]), reverse=True)):
        lang_name = lang_folders.get(lang, lang)
        active = 'active' if i == 0 else ''
        html += f'<button class="nav-tab {active}" onclick="showSection(\'sec-{lang}\')">{lang_name} ({len(lang_books)})</button>'
    html += '</div>'

    for i, (lang, lang_books) in enumerate(sorted(books_by_lang.items(), key=lambda x: len(x[1]), reverse=True)):
        lang_name = lang_folders.get(lang, lang)
        display = 'block' if i == 0 else 'none'
        html += f'<div id="sec-{lang}" class="language-section" style="display: {display};">'
        html += f'<h2 class="lang-title">{lang_name} ({len(lang_books)} 本)</h2>'

        books_by_cat = defaultdict(list)
        for meta in lang_books:
            books_by_cat[meta.category or '其他'].append(meta)

        for cat in sorted(books_by_cat.keys(), key=lambda x: len(books_by_cat[x]), reverse=True):
            cat_books = books_by_cat[cat]
            html += f'<h3 class="category-title">{cat} ({len(cat_books)} 本)</h3>'
            html += '<div class="book-grid">'

            for meta in sorted(cat_books, key=lambda x: x.title or os.path.basename(x.file_path)):
                title = meta.title or os.path.splitext(os.path.basename(meta.file_path))[0]
                author = meta.author or '未知作者'
                file_size = format_size(meta.file_size)

                if hasattr(meta, 'thumb_filename') and meta.thumb_filename:
                    cover_html = f'<img src="thumbs/{meta.thumb_filename}" class="book-cover" alt="{title}">'
                else:
                    cover_html = f'<div class="book-cover no-cover">{title[:30]}<br><span style="font-size:0.8em;opacity:0.8;">[{meta.file_type.upper()}]</span></div>'

                badge_class = f'badge-lang-{lang}' if lang in ['zh', 'en', 'ja', 'unknown'] else ''

                html += f'''
<div class="book-card">
    {cover_html}
    <div class="book-title" title="{title}">{title}</div>
    <div class="book-author" title="{author}">{author}</div>
    <div class="book-meta">
        <span class="badge {badge_class}">{meta.file_type.upper()}</span>
        <span>{file_size}</span>
    </div>
</div>
'''

            html += '</div>'

        html += '</div>'

    html += '''
</div>
<footer>
    由电子书分类工具自动生成 · 共 ''' + str(total_count) + ''' 本书籍
</footer>
<script>
function showSection(id) {
    document.querySelectorAll('.language-section').forEach(sec => {
        sec.style.display = 'none';
    });
    document.getElementById(id).style.display = 'block';
    document.querySelectorAll('.nav-tab').forEach(tab => {
        tab.classList.remove('active');
    });
    event.target.classList.add('active');
}
</script>
</body>
</html>
'''

    html_path = os.path.join(output_dir, 'index.html')
    with open(html_path, 'w', encoding='utf-8') as f:
        f.write(html)

    return html_path


def move_books(books, target_dir, rules, dry_run=False):
    """移动书籍到目标文件夹"""
    lang_folders = rules.get('language_folders', {})
    moved_count = 0
    errors = []

    for meta in books:
        lang = meta.detected_language
        lang_folder = lang_folders.get(lang, lang_folders.get('unknown', '待处理'))

        if lang == 'unknown':
            target_subdir = os.path.join(target_dir, lang_folder)
        else:
            category = meta.category or rules.get('default_category', '其他')
            target_subdir = os.path.join(target_dir, lang_folder, category)

        filename = os.path.basename(meta.file_path)
        target_path = os.path.join(target_subdir, filename)

        if os.path.abspath(meta.file_path) == os.path.abspath(target_path):
            continue

        counter = 1
        while os.path.exists(target_path):
            name, ext = os.path.splitext(filename)
            target_path = os.path.join(target_subdir, f"{name}_{counter}{ext}")
            counter += 1

        meta.target_path = target_path

        if dry_run:
            print(f"[预览] {os.path.basename(meta.file_path)} -> {os.path.relpath(target_path, target_dir)}")
            moved_count += 1
        else:
            try:
                os.makedirs(target_subdir, exist_ok=True)
                shutil.move(meta.file_path, target_path)
                moved_count += 1
            except Exception as e:
                errors.append((meta.file_path, str(e)))
                print(f"移动失败 {meta.file_path}: {e}")

    return moved_count, errors


def load_rules(config_path):
    """加载分类规则"""
    with open(config_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser(description='电子书分类整理工具')
    parser.add_argument('source_dir', help='源文件夹路径')
    parser.add_argument('-o', '--output-dir', help='输出文件夹路径（默认与源文件夹相同）')
    parser.add_argument('-c', '--config', default='category_rules.json', help='分类规则配置文件路径')
    parser.add_argument('--dry-run', action='store_true', help='预览模式，不实际移动文件')
    parser.add_argument('--no-html', action='store_true', help='不生成HTML索引页')
    parser.add_argument('--no-stats', action='store_true', help='不输出统计报表')

    args = parser.parse_args()

    source_dir = os.path.abspath(args.source_dir)
    if not os.path.isdir(source_dir):
        print(f"错误: 源文件夹不存在: {source_dir}")
        sys.exit(1)

    output_dir = os.path.abspath(args.output_dir) if args.output_dir else source_dir

    config_path = os.path.abspath(args.config)
    if not os.path.isfile(config_path):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        config_path = os.path.join(script_dir, args.config)
        if not os.path.isfile(config_path):
            print(f"错误: 配置文件不存在: {args.config}")
            sys.exit(1)

    rules = load_rules(config_path)
    text_detection_chars = rules.get('text_detection_chars', 2000)

    print(f"扫描文件夹: {source_dir}")
    print(f"配置文件: {config_path}")
    if args.dry_run:
        print("模式: 预览（不移动文件）")
    print()

    books_info = scan_books(source_dir)
    print(f"找到 {len(books_info)} 本电子书")

    if not books_info:
        print("没有找到任何电子书文件")
        return

    if not HAS_PYPDF2:
        print("提示: 未安装 PyPDF2，PDF 元数据读取将受限，可通过 pip install PyPDF2 安装")
    if not HAS_EBOOKLIB:
        print("提示: 未安装 ebooklib，将使用基础方式解析 EPUB，可通过 pip install ebooklib 安装")
    if not HAS_PIL:
        print("提示: 未安装 Pillow，无法生成封面缩略图，可通过 pip install Pillow 安装")

    print("\n正在读取元数据...")
    books_meta = []
    for i, (filepath, file_type) in enumerate(books_info, 1):
        print(f"  [{i}/{len(books_info)}] {os.path.basename(filepath)}")
        meta = read_metadata(filepath, file_type)
        lang, conf = detect_book_language(meta, text_detection_chars)
        meta.detected_language = lang
        meta.language_confidence = conf

        category = classify_book(meta, rules)
        meta.category = category

        books_meta.append(meta)

    lang_stats, unprocessed = generate_statistics(books_meta, rules)

    if not args.no_stats:
        print_statistics(lang_stats, rules, unprocessed)

    if not args.no_html:
        print("\n正在生成HTML索引页...")
        html_path = generate_html_index(books_meta, rules, output_dir)
        print(f"HTML索引页已生成: {html_path}")

    print("\n正在整理文件...")
    moved_count, errors = move_books(books_meta, output_dir, rules, dry_run=args.dry_run)

    print(f"\n{'预览' if args.dry_run else '移动'}完成！")
    print(f"  共处理: {moved_count} 个文件")
    if errors:
        print(f"  失败: {len(errors)} 个文件")
    if unprocessed:
        print(f"  待处理（无法识别语言）: {len(unprocessed)} 个文件")

    if not args.dry_run:
        print(f"\n文件已整理到: {output_dir}")
    else:
        print(f"\n这是预览模式，文件未被移动。去掉 --dry-run 参数即可实际移动文件。")


if __name__ == '__main__':
    main()
