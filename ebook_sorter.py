#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
电子书分类整理工具
扫描指定文件夹中的EPUB、PDF、MOBI文件，按语言和类别自动分类整理。
"""

import os
import sys
import json
import csv
import shutil
import argparse
import zipfile
import re
import hashlib
from pathlib import Path
from collections import defaultdict
from datetime import datetime
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple

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
CONFLICT_SKIP = 'skip'
CONFLICT_OVERWRITE = 'overwrite'
CONFLICT_RENAME = 'rename'
VALID_CONFLICT_STRATEGIES = [CONFLICT_SKIP, CONFLICT_OVERWRITE, CONFLICT_RENAME]
OPERATION_LOG_FILENAME = '.ebook_sorter_operations.json'
PLAN_FILENAME = '.ebook_sorter_plan.json'


@dataclass
class BookMetadata:
    """电子书元数据"""
    title: str = ''
    author: str = ''
    language: str = ''
    publisher: str = ''
    pub_date: str = ''
    description: str = ''
    cover_image: Optional[bytes] = None
    cover_ext: str = '.jpg'
    file_path: str = ''
    file_size: int = 0
    file_type: str = ''
    detected_language: str = ''
    language_confidence: float = 0.0
    category: str = ''
    category_confidence: float = 0.0
    target_path: str = ''
    original_path: str = ''
    move_status: str = 'pending'
    conflict_status: str = 'none'
    error_msg: str = ''
    text_preview: str = ''
    language_sources: Dict[str, Tuple[str, float]] = field(default_factory=dict)
    category_keywords_hit: Dict[str, List[str]] = field(default_factory=dict)
    thumb_filename: str = ''
    md5_hash: str = ''
    review_flags: List[str] = field(default_factory=list)
    operation_id: str = ''


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
    """通过文件名猜测语言（权重较低）"""
    name = Path(filename).stem
    lang, conf = detect_language_by_chars(name)
    return (lang, conf)


def _has_cjk_chars(text):
    """检测文本中是否含有中日韩字符"""
    if not text:
        return False
    for ch in text:
        # CJK统一表意文字, 日文平假名片假名, 韩文
        if ('\u4e00' <= ch <= '\u9fff' or '\u3400' <= ch <= '\u4dbf'
                or '\u3040' <= ch <= '\u30ff' or '\u30a0' <= ch <= '\u30ff'
                or '\uac00' <= ch <= '\ud7af' or '\u1100' <= ch <= '\u11ff'):
            return True
    return False


def detect_book_language(meta, text_detection_chars=2000, rules=None):
    """
    综合判断书籍语言 v2.0
    
    核心改进：
    - 当正文检测到中日韩字符时，**无条件优先**判断为对应 CJK 语言
    - 元数据中的 language 字段仅作参考，权重降低，且当与正文冲突时忽略
    - 强制正文采样：所有初判为英文的结果都必须经过正文验证
    - 英文文件名权重极低，不再能主导判断结果
    - 中文内容+英文文件名的书一定按正文归入中文
    
    Args:
        meta: BookMetadata 对象
        text_detection_chars: 正文采样字符数
        rules: 完整规则配置，取 language_detection 节
    """
    lang_config = rules.get('language_detection', {}) if rules else {}
    trust_metadata_cjk_only = lang_config.get('trust_metadata_only_if_cjk', True)
    body_weight_mult = lang_config.get('body_text_weight_multiplier', 1.5)
    filename_en_weight = lang_config.get('filename_en_weight', 0.1)
    force_body_check_en = lang_config.get('force_body_check_if_en', True)
    min_cjk_chars = lang_config.get('minimum_body_chars_for_cjk', 5)

    lang_sources = {}
    has_cjk_anywhere = False
    cjk_char_count = 0

    combined_short_text = " ".join(filter(None, [
        meta.title,
        meta.description,
        os.path.splitext(os.path.basename(meta.file_path))[0]
    ]))
    if _has_cjk_chars(combined_short_text):
        has_cjk_anywhere = True
        for ch in combined_short_text:
            if ('\u4e00' <= ch <= '\u9fff' or '\u3400' <= ch <= '\u4dbf'
                    or '\u3040' <= ch <= '\u30ff' or '\uac00' <= ch <= '\ud7af'):
                cjk_char_count += 1

    if meta.language:
        meta_lang = meta.language
        if trust_metadata_cjk_only:
            if meta_lang in {'zh', 'ja', 'ko'} and has_cjk_anywhere:
                lang_sources['metadata'] = (meta_lang, 0.7)
            elif meta_lang in {'zh', 'ja', 'ko'} and not has_cjk_anywhere:
                lang_sources['metadata'] = (meta_lang, 0.3)
            else:
                lang_sources['metadata'] = (meta_lang, 0.3)
        else:
            lang_sources['metadata'] = (meta_lang, 0.6)

    filename_lang, filename_conf = detect_language_by_filename(os.path.basename(meta.file_path))
    if filename_lang != 'unknown':
        if filename_lang == 'en':
            weight = filename_en_weight
        else:
            weight = 0.25
        lang_sources['filename'] = (filename_lang, filename_conf * weight)

    if meta.title:
        title_lang, title_conf = detect_language_by_chars(meta.title)
        if title_lang != 'unknown':
            weight = 0.3 if title_lang == 'en' else 0.55
            lang_sources['title'] = (title_lang, title_conf * weight)

    if meta.description:
        desc_lang, desc_conf = detect_language_by_chars(meta.description)
        if desc_lang != 'unknown':
            weight = 0.5 if desc_lang == 'en' else 0.8
            lang_sources['description'] = (desc_lang, desc_conf * weight)

    text = get_book_text_preview(meta.file_path, meta.file_type, text_detection_chars)
    body_cjk_count = 0
    if text:
        meta.text_preview = text[:500]
        text_lang, text_conf = detect_language_by_chars(text)
        for ch in text[:2000]:
            if ('\u4e00' <= ch <= '\u9fff' or '\u3400' <= ch <= '\u4dbf'
                    or '\u3040' <= ch <= '\u30ff' or '\uac00' <= ch <= '\ud7af'):
                body_cjk_count += 1
                cjk_char_count += 1
        if body_cjk_count >= min_cjk_chars:
            has_cjk_anywhere = True

        if text_lang != 'unknown':
            base_weight = 0.9 if text_lang == 'en' else 1.0
            weight = base_weight * body_weight_mult
            if text_lang in {'zh', 'ja', 'ko'} and body_cjk_count >= min_cjk_chars:
                weight = max(weight, 2.0)
            lang_sources['body_text'] = (text_lang, text_conf * weight)

    if not lang_sources:
        return ('unknown', 0)

    if has_cjk_anywhere and cjk_char_count >= min_cjk_chars:
        cjk_candidates = {'zh': 0.0, 'ja': 0.0, 'ko': 0.0}
        for src_name, (lang, conf) in lang_sources.items():
            if lang in cjk_candidates:
                cjk_candidates[lang] += conf

        best_cjk_lang = max(cjk_candidates, key=cjk_candidates.get)
        best_cjk_score = cjk_candidates[best_cjk_lang]

        if best_cjk_score > 0.2:
            lang_sources = {
                k: v for k, v in lang_sources.items()
                if v[0] in {'zh', 'ja', 'ko'}
            }
            if not lang_sources:
                lang_sources['body_text'] = (best_cjk_lang, max(best_cjk_score, 0.8))
            if 'metadata' in lang_sources and lang_sources['metadata'][0] == 'en':
                del lang_sources['metadata']

    if force_body_check_en and not text:
        candidates = list(lang_sources.values())
        if candidates:
            temp_scores = defaultdict(float)
            for l, c in candidates:
                temp_scores[l] += c
            top_lang = max(temp_scores, key=temp_scores.get)
            if top_lang == 'en' and not has_cjk_anywhere:
                try:
                    text = get_book_text_preview(meta.file_path, meta.file_type, text_detection_chars)
                    if text:
                        meta.text_preview = text[:500]
                        text_lang, text_conf = detect_language_by_chars(text)
                        if text_lang != 'unknown':
                            weight = 0.9 * body_weight_mult
                            lang_sources['body_text'] = (text_lang, text_conf * weight)
                except Exception:
                    pass

    if not lang_sources:
        return ('unknown', 0)

    lang_scores = defaultdict(float)
    for src_name, (lang, conf) in lang_sources.items():
        lang_scores[lang] += conf

    best_lang = max(lang_scores, key=lang_scores.get)
    best_score = lang_scores[best_lang]

    for k, v in lang_sources.items():
        meta.language_sources[k] = v

    return (best_lang, round(best_score, 3))


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
    """
    根据规则对书籍进行子分类 v2.0
    
    改进特性：
    - 综合文件名、书名、简介、正文片段判断
    - 支持同义词映射（Python = python = py）
    - 支持排除词（命中则该分类被排除）
    - 支持作者和出版社辅助判断（匹配则直接加分）
    - 高优先级关键词（命中直接大幅加分，无需多处出现）
    - 元数据缺失时也能通过文件名+正文正确分类
    
    返回: (分类名, 置信度)
    """
    lang = meta.detected_language
    default_cat = rules.get('default_category', '其他')

    if lang not in rules.get('subcategories', {}):
        meta.category_confidence = 0.0
        meta.category_keywords_hit = {}
        return default_cat

    subcategories = rules['subcategories'][lang]

    filename_only = os.path.splitext(os.path.basename(meta.file_path))[0]
    if not meta.text_preview:
        try:
            preview = get_book_text_preview(meta.file_path, meta.file_type, 3000)
            meta.text_preview = preview[:500] if preview else ''
        except Exception:
            pass

    text_parts = [
        (filename_only, 0.9),
        (meta.title or '', 1.2),
        (meta.description or '', 1.5),
        (meta.text_preview or '', 1.8),
    ]

    all_text_lower = " ".join([t for t, _ in text_parts if t]).lower()
    author_lower = (meta.author or '').lower()
    publisher_lower = (meta.publisher or '').lower()

    category_scores = {}
    category_keywords_hit = defaultdict(list)
    category_excluded = set()

    global_excludes = [kw.lower() for kw in rules.get('global_exclude_keywords', [])]
    for excl in global_excludes:
        if excl in all_text_lower:
            pass

    for cat_name, cat_info in sorted(subcategories.items(), key=lambda x: x[1].get('priority', 99)):
        keywords = cat_info.get('keywords', [])
        high_priority_kw = cat_info.get('high_priority_keywords', [])
        synonyms = cat_info.get('synonyms', {})
        exclude_keywords = cat_info.get('exclude_keywords', [])
        target_authors = cat_info.get('authors', [])
        target_publishers = cat_info.get('publishers', [])
        priority_weight = 1.0 / cat_info.get('priority', 1)

        total_score = 0.0

        for excl_kw in exclude_keywords:
            if excl_kw.lower() in all_text_lower:
                category_excluded.add(cat_name)
                break

        if cat_name in category_excluded:
            continue

        for target_author in target_authors:
            if target_author.lower() in author_lower:
                total_score += 10.0
                category_keywords_hit[cat_name].append(f"[作者:{target_author}]")

        for target_pub in target_publishers:
            if target_pub.lower() in publisher_lower:
                total_score += 5.0
                category_keywords_hit[cat_name].append(f"[出版社:{target_pub}]")

        for hp_kw in high_priority_kw:
            hp_kw_lower = hp_kw.lower()
            if hp_kw_lower in all_text_lower:
                count = all_text_lower.count(hp_kw_lower)
                if count > 0:
                    total_score += count * 15.0 * priority_weight
                    category_keywords_hit[cat_name].append(f"★{hp_kw}x{count}")

        expanded_keywords = list(keywords)
        for main_kw, syn_list in synonyms.items():
            for syn in syn_list:
                if main_kw not in expanded_keywords:
                    expanded_keywords.append(main_kw)

        for text, source_weight in text_parts:
            if not text:
                continue
            text_lower = text.lower()
            for keyword in expanded_keywords:
                kw_lower = keyword.lower()
                count = text_lower.count(kw_lower)
                if count > 0:
                    kw_len_weight = min(1.0, len(keyword) / 10.0) + 0.5
                    hit_score = count * priority_weight * source_weight * kw_len_weight
                    total_score += hit_score
                    category_keywords_hit[cat_name].append(f"{keyword}x{count}")

                    syn_list = synonyms.get(keyword, [])
                    for syn in syn_list:
                        syn_count = text_lower.count(syn.lower())
                        if syn_count > 0:
                            total_score += syn_count * priority_weight * source_weight * 0.7
                            category_keywords_hit[cat_name].append(f"{keyword}→{syn}x{syn_count}")

        if total_score > 0:
            category_scores[cat_name] = round(total_score, 3)

    if category_scores:
        sorted_cats = sorted(category_scores.items(), key=lambda x: x[1], reverse=True)
        best_cat, best_score = sorted_cats[0]

        meta.category_confidence = best_score
        if best_cat in category_keywords_hit:
            meta.category_keywords_hit[best_cat] = list(dict.fromkeys(category_keywords_hit[best_cat]))[:10]
        return best_cat

    meta.category_confidence = 0.0
    meta.category_keywords_hit = {}
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


def save_operation_log(books, output_dir, operation_id):
    """保存操作记录，用于后续撤销"""
    log_path = os.path.join(output_dir, OPERATION_LOG_FILENAME)
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

    operations = []
    for meta in books:
        if meta.move_status in ('success', 'in_place'):
            operations.append({
                'operation_id': operation_id,
                'original_path': meta.original_path or meta.file_path,
                'current_path': meta.target_path or meta.file_path,
                'filename': os.path.basename(meta.file_path),
                'file_size': meta.file_size,
                'detected_language': meta.detected_language,
                'category': meta.category,
                'moved_at': timestamp,
                'md5_hash': meta.md5_hash,
                'conflict_status': meta.conflict_status,
            })

    existing_log = []
    if os.path.exists(log_path):
        try:
            with open(log_path, 'r', encoding='utf-8') as f:
                existing_log = json.load(f)
        except Exception:
            existing_log = []

    existing_log.extend(operations)

    try:
        with open(log_path, 'w', encoding='utf-8') as f:
            json.dump(existing_log, f, ensure_ascii=False, indent=2)
        return log_path
    except Exception as e:
        print(f"保存操作记录失败: {e}")
        return None


def load_operation_log(output_dir):
    """加载操作记录"""
    log_path = os.path.join(output_dir, OPERATION_LOG_FILENAME)
    if not os.path.exists(log_path):
        return []
    try:
        with open(log_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception:
        return []


def undo_operations(output_dir, operation_id=None):
    """
    撤销操作，尽量还原文件到原路径
    
    Args:
        output_dir: 输出目录
        operation_id: 指定撤销某次操作，None 则撤销最近一次
    
    Returns:
        (成功数量, 失败列表, 跳过列表)
    """
    all_ops = load_operation_log(output_dir)
    if not all_ops:
        return (0, [], ["没有找到任何操作记录"])

    ops_to_undo = []
    if operation_id:
        ops_to_undo = [op for op in all_ops if op['operation_id'] == operation_id]
        if not ops_to_undo:
            return (0, [], [f"没有找到操作ID: {operation_id}"])
    else:
        if all_ops:
            last_id = all_ops[-1]['operation_id']
            ops_to_undo = [op for op in all_ops if op['operation_id'] == last_id]

    success_count = 0
    failed = []
    skipped = []

    ops_to_undo.reverse()

    remaining_ops = [op for op in all_ops if op not in ops_to_undo]

    for op in ops_to_undo:
        src = op['current_path']
        dst = op['original_path']
        filename = op['filename']

        if not os.path.exists(src):
            skipped.append({
                'file': filename,
                'reason': f'源文件不存在: {src}',
                'original_path': dst,
            })
            continue

        if os.path.abspath(src) == os.path.abspath(dst):
            skipped.append({
                'file': filename,
                'reason': '文件就在原位置，无需移动',
                'original_path': dst,
            })
            continue

        if os.path.exists(dst):
            try:
                dst_size = os.path.getsize(dst)
                if dst_size == op['file_size']:
                    skipped.append({
                        'file': filename,
                        'reason': f'目标路径已存在同名同大小文件，可能已被还原: {dst}',
                        'original_path': dst,
                    })
                    continue
                else:
                    base, ext = os.path.splitext(dst)
                    counter = 1
                    while os.path.exists(dst):
                        dst = f"{base}_restored_{counter}{ext}"
                        counter += 1
            except Exception:
                pass

        try:
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.move(src, dst)
            success_count += 1
            remaining_ops = [op2 for op2 in remaining_ops if op2['current_path'] != op['current_path']]
        except Exception as e:
            failed.append({
                'file': filename,
                'reason': str(e),
                'src': src,
                'dst': dst,
            })

    log_path = os.path.join(output_dir, OPERATION_LOG_FILENAME)
    try:
        with open(log_path, 'w', encoding='utf-8') as f:
            json.dump(remaining_ops, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"更新操作记录失败: {e}")

    return (success_count, failed, skipped)


def generate_plan(books, output_dir, rules, conflict_strategy=CONFLICT_RENAME):
    """
    生成整理计划（不实际移动文件），保存到 JSON 文件供确认
    """
    temp_books = []
    for meta in books:
        m = BookMetadata()
        for key, value in meta.__dict__.items():
            if key not in ['cover_image']:
                try:
                    setattr(m, key, value)
                except Exception:
                    pass
        temp_books.append(m)

    _, _, conflicts = move_books(temp_books, output_dir, rules, dry_run=True, conflict_strategy=conflict_strategy)

    plan_data = {
        'plan_id': datetime.now().strftime('%Y%m%d_%H%M%S'),
        'generated_at': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
        'source_dir': books[0].file_path if books else '',
        'output_dir': output_dir,
        'conflict_strategy': conflict_strategy,
        'total_books': len(temp_books),
        'conflicts_count': len(conflicts),
        'conflicts': conflicts,
        'books': [],
    }

    lang_folders = rules.get('language_folders', {})
    for meta in temp_books:
        lang_name = lang_folders.get(meta.detected_language, meta.detected_language)
        sources_str = '; '.join(
            [f"{src}:{lang}({conf:.2f})" for src, (lang, conf) in meta.language_sources.items()]
        ) if meta.language_sources else ''

        hit_keywords = ''
        if meta.category_keywords_hit and meta.category in meta.category_keywords_hit:
            hit_keywords = ', '.join(meta.category_keywords_hit[meta.category])

        flags = _get_review_flags(meta)

        plan_data['books'].append({
            'filename': os.path.basename(meta.file_path),
            'original_path': meta.file_path,
            'planned_path': meta.target_path,
            'file_type': meta.file_type,
            'file_size': meta.file_size,
            'file_size_display': format_size(meta.file_size),
            'detected_language': meta.detected_language,
            'language_name': lang_name,
            'language_confidence': meta.language_confidence,
            'language_sources': sources_str,
            'category': meta.category,
            'category_confidence': meta.category_confidence,
            'keywords_hit': hit_keywords,
            'title': meta.title,
            'author': meta.author,
            'conflict_status': meta.conflict_status,
            'review_flags': flags,
        })

    plan_path = os.path.join(output_dir, PLAN_FILENAME)
    try:
        with open(plan_path, 'w', encoding='utf-8') as f:
            json.dump(plan_data, f, ensure_ascii=False, indent=2)
        return plan_path, plan_data, temp_books
    except Exception as e:
        print(f"生成计划文件失败: {e}")
        return None, None, temp_books


def load_plan(output_dir):
    """加载已生成的计划"""
    plan_path = os.path.join(output_dir, PLAN_FILENAME)
    if not os.path.exists(plan_path):
        return None
    try:
        with open(plan_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception:
        return None


def print_plan_summary(plan_data):
    """打印计划摘要"""
    if not plan_data:
        return

    print(f"\n{'═' * 60}")
    print(f"📋 整理计划摘要 (ID: {plan_data['plan_id']})")
    print(f"{'─' * 60}")
    print(f"  📖 书籍总数:       {plan_data['total_books']}")
    print(f"  📁 输出目录:       {plan_data['output_dir']}")
    print(f"  ⚙️  冲突策略:       {plan_data['conflict_strategy']}")
    print(f"  ⚠️  冲突数量:       {plan_data['conflicts_count']}")

    lang_stats = defaultdict(int)
    cat_stats = defaultdict(int)
    flag_stats = defaultdict(int)

    for book in plan_data['books']:
        lang_stats[book['language_name']] += 1
        cat_stats[book['category']] += 1
        for flag in book['review_flags']:
            flag_stats[flag] += 1

    print(f"\n  📊 语言分布:")
    for lang, cnt in sorted(lang_stats.items(), key=lambda x: -x[1]):
        print(f"    - {lang}: {cnt} 本")

    print(f"\n  📂 分类分布:")
    for cat, cnt in sorted(cat_stats.items(), key=lambda x: -x[1]):
        print(f"    - {cat}: {cnt} 本")

    if flag_stats:
        print(f"\n  🚩 需要复核:")
        for flag, cnt in sorted(flag_stats.items(), key=lambda x: -x[1]):
            print(f"    - {flag}: {cnt} 本")

    if plan_data['conflicts']:
        print(f"\n  ⚠️  冲突列表:")
        for i, cf in enumerate(plan_data['conflicts'][:20], 1):
            print(f"    [{i}] {cf['file']} -> {cf['action']}")
            if cf.get('renamed_to'):
                print(f"         重命名为: {cf['renamed_to']}")
        if len(plan_data['conflicts']) > 20:
            print(f"    ... 还有 {len(plan_data['conflicts']) - 20} 个冲突，详见计划文件")

    print(f"\n{'═' * 60}")


def _get_review_flags(meta):
    """获取需要复核的标签"""
    flags = []
    if meta.detected_language == 'unknown':
        flags.append('未知语言')
    if meta.language_confidence < 0.4 and meta.detected_language != 'unknown':
        flags.append('低语言置信度')
    if meta.category_confidence < 0.5 and meta.category_confidence > 0:
        flags.append('低分类置信度')
    if meta.category == '其他':
        flags.append('未分类')
    if meta.conflict_status != 'none':
        flags.append('文件冲突')
    if meta.move_status == 'failed':
        flags.append('移动失败')
    filename_lang, _ = detect_language_by_filename(os.path.basename(meta.file_path))
    if filename_lang == 'en' and meta.detected_language == 'zh':
        flags.append('英文件名中内容')
    if meta.language and meta.language.startswith('en') and meta.detected_language == 'zh':
        flags.append('元数据误标')
    return flags


def export_manifest(books, output_dir, rules, format='both'):
    """
    导出整理清单（CSV和JSON格式）
    
    v2.0 改进：
    - 增加复核标签列，低置信度/冲突/未知语言等特殊情况单独标记
    - 增加关键词命中列，显示分类依据
    - 便于在Excel中直接筛选复核
    """
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    csv_path = os.path.join(output_dir, f'整理清单_{timestamp}.csv')
    json_path = os.path.join(output_dir, f'整理清单_{timestamp}.json')

    lang_folders = rules.get('language_folders', {})
    rows = []

    for meta in books:
        lang_name = lang_folders.get(meta.detected_language, meta.detected_language)
        sources_str = '; '.join(
            [f"{src}:{lang}({conf:.2f})" for src, (lang, conf) in meta.language_sources.items()]
        ) if meta.language_sources else ''

        flags = _get_review_flags(meta)
        flags_str = '|'.join(flags) if flags else ''

        hit_keywords = ''
        if hasattr(meta, 'category_keywords_hit') and meta.category_keywords_hit:
            if meta.category in meta.category_keywords_hit:
                hit_keywords = ', '.join(meta.category_keywords_hit[meta.category])

        row = {
            '🚩复核标签': flags_str,
            '文件名': os.path.basename(meta.file_path),
            '原路径': meta.original_path or meta.file_path,
            '新路径': meta.target_path or '',
            '文件类型': meta.file_type,
            '文件大小': format_size(meta.file_size),
            '识别语言': lang_name,
            '语言代码': meta.detected_language,
            '语言置信度': round(meta.language_confidence, 3),
            '语言判断来源': sources_str,
            '二级分类': meta.category,
            '分类置信度': round(meta.category_confidence, 3),
            '分类依据关键词': hit_keywords,
            '书名': meta.title or '',
            '作者': meta.author or '',
            '出版社': meta.publisher or '',
            '冲突状态': meta.conflict_status,
            '移动状态': meta.move_status,
            '错误信息': meta.error_msg,
        }
        rows.append(row)

    rows.sort(key=lambda r: (0 if r['🚩复核标签'] else 1, r['🚩复核标签'], r['识别语言'], r['二级分类']))

    exported = []

    if format in ('csv', 'both'):
        try:
            with open(csv_path, 'w', encoding='utf-8-sig', newline='') as f:
                if rows:
                    writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
                    writer.writeheader()
                    writer.writerows(rows)
            exported.append(f'CSV: {csv_path}')
        except Exception as e:
            print(f"导出CSV清单失败: {e}")

    if format in ('json', 'both'):
        try:
            full_data = {
                '生成时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                '总数量': len(rows),
                '需要复核数量': sum(1 for r in rows if r['🚩复核标签']),
                '文件列表': rows,
                '统计': {
                    '语言分布': {},
                    '分类分布': {},
                    '成功数量': sum(1 for m in books if m.move_status in ('success', 'planned', 'in_place')),
                    '跳过数量': sum(1 for m in books if m.move_status == 'skipped'),
                    '冲突数量': sum(1 for m in books if m.conflict_status != 'none'),
                    '失败数量': sum(1 for m in books if m.move_status == 'failed'),
                    '待处理数量': sum(1 for m in books if m.detected_language == 'unknown'),
                    '低置信度数量': sum(1 for m in books if m.language_confidence < 0.4 and m.detected_language != 'unknown'),
                    '未分类数量': sum(1 for m in books if m.category == '其他'),
                }
            }
            for meta in books:
                lang = meta.detected_language
                ln = lang_folders.get(lang, lang)
                full_data['统计']['语言分布'][ln] = full_data['统计']['语言分布'].get(ln, 0) + 1
                if meta.category:
                    full_data['统计']['分类分布'][meta.category] = full_data['统计']['分类分布'].get(meta.category, 0) + 1

            with open(json_path, 'w', encoding='utf-8') as f:
                json.dump(full_data, f, ensure_ascii=False, indent=2)
            exported.append(f'JSON: {json_path}')
        except Exception as e:
            print(f"导出JSON清单失败: {e}")

    return exported


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


def move_books(books, target_dir, rules, dry_run=False, conflict_strategy=CONFLICT_RENAME):
    """
    移动书籍到目标文件夹
    
    冲突处理策略：
    - skip: 跳过同名文件
    - overwrite: 覆盖目标文件
    - rename: 自动重命名 (默认)
    
    返回: (处理数量, 错误列表, 冲突列表)
    """
    lang_folders = rules.get('language_folders', {})
    processed_count = 0
    errors = []
    conflicts = []
    reserved_targets = set()

    for meta in books:
        lang = meta.detected_language
        lang_folder = lang_folders.get(lang, lang_folders.get('unknown', '待处理'))

        if lang == 'unknown':
            target_subdir = os.path.join(target_dir, lang_folder)
        else:
            category = meta.category or rules.get('default_category', '其他')
            target_subdir = os.path.join(target_dir, lang_folder, category)

        filename = os.path.basename(meta.file_path)
        base_name, ext = os.path.splitext(filename)
        target_path = os.path.join(target_subdir, filename)

        src_abs = os.path.abspath(meta.file_path)
        dst_abs = os.path.abspath(target_path)

        if src_abs == dst_abs:
            meta.move_status = 'in_place'
            meta.target_path = dst_abs
            processed_count += 1
            continue

        has_disk_conflict = os.path.exists(dst_abs)
        has_batch_conflict = dst_abs in reserved_targets

        if has_disk_conflict or has_batch_conflict:
            meta.conflict_status = 'conflict'
            if conflict_strategy == CONFLICT_SKIP:
                conflicts.append({
                    'file': filename,
                    'type': '目标已存在' if has_disk_conflict else '批次内冲突',
                    'src': meta.file_path,
                    'dst': dst_abs,
                    'action': '跳过'
                })
                meta.move_status = 'skipped'
                meta.target_path = dst_abs
                meta.error_msg = '同名文件冲突，已跳过'
                continue

            elif conflict_strategy == CONFLICT_OVERWRITE:
                conflicts.append({
                    'file': filename,
                    'type': '目标已存在' if has_disk_conflict else '批次内冲突',
                    'src': meta.file_path,
                    'dst': dst_abs,
                    'action': '覆盖'
                })
                meta.conflict_status = 'overwrite'
                meta.target_path = dst_abs

            else:
                counter = 1
                final_path = dst_abs
                while True:
                    candidate_name = f"{base_name}_{counter}{ext}"
                    candidate_path = os.path.join(target_subdir, candidate_name)
                    candidate_abs = os.path.abspath(candidate_path)
                    if not os.path.exists(candidate_abs) and candidate_abs not in reserved_targets:
                        final_path = candidate_abs
                        break
                    counter += 1

                conflicts.append({
                    'file': filename,
                    'type': '目标已存在' if has_disk_conflict else '批次内冲突',
                    'src': meta.file_path,
                    'dst': dst_abs,
                    'renamed_to': os.path.basename(final_path),
                    'action': '自动重命名'
                })
                target_path = final_path
                meta.conflict_status = 'renamed'
                meta.target_path = target_path
        else:
            meta.conflict_status = 'none'
            meta.target_path = dst_abs

        reserved_targets.add(os.path.abspath(meta.target_path))

        if dry_run:
            meta.move_status = 'planned'
            rel_dst = os.path.relpath(meta.target_path, target_dir)
            conflict_tag = ''
            if meta.conflict_status == 'overwrite':
                conflict_tag = ' [将覆盖]'
            elif meta.conflict_status == 'renamed':
                conflict_tag = f' [重命名: {os.path.basename(meta.target_path)}]'
            print(f"[预览] {os.path.basename(meta.file_path)} -> {rel_dst}{conflict_tag}")
            processed_count += 1
        else:
            try:
                os.makedirs(os.path.dirname(meta.target_path), exist_ok=True)
                if conflict_strategy == CONFLICT_OVERWRITE and os.path.exists(meta.target_path):
                    os.remove(meta.target_path)
                shutil.move(meta.file_path, meta.target_path)
                meta.move_status = 'success'
                processed_count += 1
            except Exception as e:
                meta.move_status = 'failed'
                meta.error_msg = str(e)
                errors.append((meta.file_path, str(e)))
                print(f"移动失败 {meta.file_path}: {e}")

    return processed_count, errors, conflicts


def print_conflicts_summary(conflicts):
    """打印冲突摘要"""
    if not conflicts:
        return
    print(f"\n{'=' * 60}")
    print(f"冲突文件汇总 ({len(conflicts)} 个):")
    print("-" * 60)
    for i, cf in enumerate(conflicts, 1):
        print(f"  [{i}] {cf['file']}")
        print(f"       原因: {cf['type']}")
        print(f"       处理: {cf['action']}")
        if cf.get('renamed_to'):
            print(f"       重命名为: {cf['renamed_to']}")
        print()


def load_rules(config_path):
    """加载分类规则"""
    with open(config_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def main():
    parser = argparse.ArgumentParser(
        description='电子书分类整理工具 v3.0',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
示例:
  # 生成整理计划（不移动文件）
  python ebook_sorter.py "D:\\书库" --plan-only
  
  # 确认并执行上次生成的计划
  python ebook_sorter.py "D:\\书库" --confirm-plan
  
  # 直接整理（自动先生成计划再执行）
  python ebook_sorter.py "D:\\书库"
  
  # 撤销上次操作
  python ebook_sorter.py "D:\\书库" --undo
  
  # 撤销指定操作
  python ebook_sorter.py "D:\\书库" --undo-id 20260612_153000
  
  # 指定冲突处理策略
  python ebook_sorter.py "D:\\书库" --conflict skip
        '''
    )
    parser.add_argument('source_dir', nargs='?', help='源文件夹路径')
    parser.add_argument('-o', '--output-dir', help='输出文件夹路径（默认与源文件夹相同）')
    parser.add_argument('-c', '--config', default='category_rules.json', help='分类规则配置文件路径')
    parser.add_argument('--dry-run', action='store_true', help='预览模式，不实际移动文件')
    parser.add_argument('--no-html', action='store_true', help='不生成HTML索引页')
    parser.add_argument('--no-stats', action='store_true', help='不输出统计报表')
    parser.add_argument('--no-manifest', action='store_true', help='不导出整理清单')
    parser.add_argument('--plan-only', action='store_true', help='仅生成整理计划，不执行，待确认后手动执行')
    parser.add_argument('--confirm-plan', action='store_true', help='确认执行上次生成的计划')
    parser.add_argument('--y', '--yes', action='store_true', dest='auto_confirm', help='自动确认所有提示')
    parser.add_argument('--undo', action='store_true', help='撤销最近一次整理操作，还原到原路径')
    parser.add_argument('--undo-id', help='撤销指定ID的操作（见操作记录）')
    parser.add_argument(
        '--conflict',
        choices=VALID_CONFLICT_STRATEGIES,
        default=CONFLICT_RENAME,
        help=f'同名文件冲突处理策略: skip=跳过, overwrite=覆盖, rename=自动重命名 (默认: {CONFLICT_RENAME})'
    )
    parser.add_argument(
        '--manifest-format',
        choices=['csv', 'json', 'both'],
        default='both',
        help='整理清单导出格式 (默认: both)'
    )

    args = parser.parse_args()

    if args.undo or args.undo_id:
        target_dir = os.path.abspath(args.source_dir) if args.source_dir else os.getcwd()
        if not os.path.isdir(target_dir):
            target_dir = os.getcwd()
        print(f"📂 操作目录: {target_dir}")
        print(f"↩️  正在撤销{'指定' if args.undo_id else '最近一次'}操作...")
        success, failed, skipped = undo_operations(target_dir, args.undo_id)
        print(f"\n{'═' * 60}")
        print(f"↩️  撤销完成！")
        print(f"{'─' * 60}")
        print(f"  ✅ 成功还原: {success} 个文件")
        if skipped:
            print(f"  ⏭️  跳过: {len(skipped)} 个文件")
            for s in skipped[:10]:
                print(f"     - {s['file']}: {s['reason']}")
            if len(skipped) > 10:
                print(f"     ... 还有 {len(skipped) - 10} 个")
        if failed:
            print(f"  ❌ 失败: {len(failed)} 个文件")
            for f in failed[:10]:
                print(f"     - {f['file']}: {f['reason']}")
            if len(failed) > 10:
                print(f"     ... 还有 {len(failed) - 10} 个")
        print(f"{'═' * 60}")
        return

    if not args.source_dir:
        print("错误: 请指定源文件夹路径，或使用 --undo 进行撤销")
        parser.print_help()
        sys.exit(1)

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
    text_detection_chars = rules.get('text_detection_chars', 3000)
    operation_id = datetime.now().strftime('%Y%m%d_%H%M%S')

    if args.confirm_plan:
        plan_data = load_plan(output_dir)
        if not plan_data:
            print(f"❌ 在 {output_dir} 中未找到计划文件 {PLAN_FILENAME}")
            print("请先使用 --plan-only 生成计划")
            sys.exit(1)
        print_plan_summary(plan_data)
        if not args.auto_confirm:
            try:
                confirm = input("\n确认执行以上计划？(y/N): ").strip().lower()
                if confirm not in ('y', 'yes'):
                    print("已取消执行")
                    return
            except KeyboardInterrupt:
                print("\n已取消执行")
                return
        source_dir = os.path.commonpath([b['original_path'] for b in plan_data['books']]) if plan_data['books'] else source_dir
        args.conflict = plan_data['conflict_strategy']
        books_info = [(b['original_path'], b['file_type']) for b in plan_data['books']]
        print(f"\n✅ 计划已确认，开始执行 (操作ID: {operation_id})...")
    else:
        print(f"扫描文件夹: {source_dir}")
        print(f"输出文件夹: {output_dir}")
        print(f"配置文件: {config_path}")
        print(f"冲突策略: {args.conflict} (skip=跳过 / overwrite=覆盖 / rename=重命名)")
        print(f"操作ID: {operation_id}")
        if args.dry_run:
            print("⚠️  模式: 预览（不实际移动文件）")
        if args.plan_only:
            print("📋 模式: 仅生成计划")
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

    print("\n正在读取元数据并检测语言/分类...")
    books_meta = []
    low_confidence_count = 0
    lang_mismatch_count = 0
    needs_review_count = 0

    for i, (filepath, file_type) in enumerate(books_info, 1):
        display_name = os.path.basename(filepath)
        if len(display_name) > 50:
            display_name = display_name[:47] + '...'
        print(f"  [{i}/{len(books_info)}] {display_name}", end='')

        meta = read_metadata(filepath, file_type)
        meta.original_path = filepath
        meta.operation_id = operation_id
        meta.file_path = filepath

        lang, conf = detect_book_language(meta, text_detection_chars, rules=rules)
        meta.detected_language = lang
        meta.language_confidence = conf

        category = classify_book(meta, rules)
        meta.category = category

        flags = _get_review_flags(meta)
        meta.review_flags = flags
        if flags:
            needs_review_count += 1

        if conf < 0.3 and lang != 'unknown':
            low_confidence_count += 1

        filename_lang, _ = detect_language_by_filename(os.path.basename(filepath))
        if filename_lang == 'en' and lang == 'zh':
            lang_mismatch_count += 1

        books_meta.append(meta)

        status_parts = []
        lang_names = {'zh': '中文', 'en': '英文', 'ja': '日文', 'ko': '韩文', 'unknown': '待识别'}
        status_parts.append(f"语言={lang_names.get(lang, lang)}({conf:.2f})")
        cat_info = f"分类={meta.category}" if meta.category_confidence > 0 else "分类=其他"
        if meta.category_confidence > 0:
            cat_info += f"({meta.category_confidence:.1f})"
        status_parts.append(cat_info)
        if flags:
            status_parts.append(f"🚩{','.join(flags[:2])}")
        print(f"  [{', '.join(status_parts)}]")

    if args.plan_only or not args.confirm_plan:
        print(f"\n📋 正在生成整理计划...")
        plan_path, plan_data, _ = generate_plan(books_meta, output_dir, rules, conflict_strategy=args.conflict)
        print_plan_summary(plan_data)
        print(f"\n📋 计划已保存到: {plan_path}")
        if args.plan_only:
            print(f"\n💡 使用 --confirm-plan 参数确认并执行此计划")
            if not args.no_manifest:
                print("正在导出预整理清单...")
                exported = export_manifest(books_meta, output_dir, rules, format=args.manifest_format)
                for exp in exported:
                    print(f"  ✓ {exp}")
            return

    lang_stats, unprocessed = generate_statistics(books_meta, rules)

    if not args.no_stats:
        print_statistics(lang_stats, rules, unprocessed)

    if low_confidence_count > 0 or lang_mismatch_count > 0 or needs_review_count > 0:
        print(f"\n📌 质量提示:")
        if needs_review_count > 0:
            print(f"   - 需要人工复核: {needs_review_count} 本 (详见清单的 🚩复核标签 列)")
        if lang_mismatch_count > 0:
            print(f"   - 英文文件名但内容是中文: {lang_mismatch_count} 本 (已按正文内容修正为中文分类)")
        if low_confidence_count > 0:
            print(f"   - 语言判断置信度较低: {low_confidence_count} 本")

    if not args.no_html:
        print("\n正在生成HTML索引页...")
        html_path = generate_html_index(books_meta, rules, output_dir)
        print(f"  ✓ HTML索引页: {html_path}")

    if not args.confirm_plan:
        if not args.auto_confirm and not args.dry_run:
            try:
                confirm = input(f"\n确认整理以上 {len(books_meta)} 本书？(y/N): ").strip().lower()
                if confirm not in ('y', 'yes'):
                    print("已取消执行")
                    if not args.no_manifest:
                        print("正在导出预整理清单...")
                        exported = export_manifest(books_meta, output_dir, rules, format=args.manifest_format)
                        for exp in exported:
                            print(f"  ✓ {exp}")
                    return
            except KeyboardInterrupt:
                print("\n已取消执行")
                return

    print(f"\n正在整理文件（冲突策略: {args.conflict}）...")
    moved_count, errors, conflicts = move_books(
        books_meta, output_dir, rules,
        dry_run=args.dry_run,
        conflict_strategy=args.conflict
    )

    if conflicts:
        print_conflicts_summary(conflicts)

    if not args.no_manifest:
        print("\n正在导出整理清单...")
        exported = export_manifest(books_meta, output_dir, rules, format=args.manifest_format)
        for exp in exported:
            print(f"  ✓ {exp}")

    if not args.dry_run:
        log_path = save_operation_log(books_meta, output_dir, operation_id)
        if log_path:
            print(f"  ✓ 操作记录: {log_path} (用于撤销)")

    print(f"\n{'═' * 60}")
    action_label = '预览' if args.dry_run else '移动'
    print(f"📚 整理{action_label}完成！ (操作ID: {operation_id})")
    print(f"{'─' * 60}")
    success_count = sum(1 for m in books_meta if m.move_status in ('success', 'planned', 'in_place'))
    skipped_count = sum(1 for m in books_meta if m.move_status == 'skipped')
    failed_count = sum(1 for m in books_meta if m.move_status == 'failed')

    print(f"  📖 扫描总数:     {len(books_meta)}")
    print(f"  ✅ 已处理:       {success_count}")
    if conflicts:
        overwrite_n = sum(1 for c in conflicts if c['action'] == '覆盖')
        rename_n = sum(1 for c in conflicts if c['action'] == '自动重命名')
        skip_n = sum(1 for c in conflicts if c['action'] == '跳过')
        parts = []
        if overwrite_n:
            parts.append(f"覆盖{overwrite_n}")
        if rename_n:
            parts.append(f"重命名{rename_n}")
        if skip_n:
            parts.append(f"跳过{skip_n}")
        print(f"  ⚠️  冲突数量:     {len(conflicts)} ({', '.join(parts)})")
    if needs_review_count > 0:
        print(f"  🚩 需复核:       {needs_review_count} (打开CSV筛选🚩列即可查看)")
    if skipped_count:
        print(f"  ⏭️  已跳过:       {skipped_count}")
    if failed_count:
        print(f"  ❌ 失败数量:     {failed_count}")
    if unprocessed:
        print(f"  ❓ 待处理(未知): {len(unprocessed)} （位于「待处理」文件夹）")

    print(f"\n  📁 输出目录: {output_dir}")

    if not args.no_html:
        print(f"  🌐 HTML索引: file:///{html_path.replace(os.sep, '/')}")

    if not args.dry_run:
        print(f"\n↩️  撤销操作: python ebook_sorter.py \"{output_dir}\" --undo")
        print(f"   或指定ID: python ebook_sorter.py \"{output_dir}\" --undo-id {operation_id}")
    else:
        print(f"\n💡 这是预览模式，文件未被移动。")
        print(f"   确认无误后去掉 --dry-run 参数即可实际移动文件。")
    print(f"{'═' * 60}")


if __name__ == '__main__':
    main()
