"""
‎باك إند ترجمة ملفات PDF - يستبدل النص الإنجليزي فعلياً بالعربي داخل بنية الملف

‎نسخة معدّلة تحل:
‎  1) اختفاء البولد (كان يأخذ التنسيق من أول span بس ويهمل flags)
‎  2) تراكب الأيقونات فوق النص (كان يرسم الصور بعد النص دايمًا)
‎  3) انكسار السمارت آرت (كان يعكس النص والصور بس، ويترك الأشكال المتجهية
‎     [مربعات/أسهم/خطوط الرسم التنظيمي] بمكانها الأصلية)
‎  4) اختفاء صور الخلفية عند فشل إعادة الإدراج (كان يمسح صمت بدون fallback)
‎  5) فيضان النص خارج حدود صندوقه (كان يرسم بحجم خط ثابت بدون تحقق من العرض)
‎  6) خلفيات شرائح الفواصل الكاملة تختفي (تُترك بحالها الآن، بدون مسح ولا إعادة رسم)
‎  7) مربع أسود مكان أيقونة الدبوس الشفافة (اللقطة المُركّبة صارت الأساس، مو fallback،
‎     لأن البايتات الخام تفقد الشفافية بصمت بدون Exception)

‎  ── إصلاحات جديدة (الجولة الثانية) ──
‎  8) الهايلايت/اللون يطلع على السطر كامل بدل الكلمة صاحبة اللون فعليًا:
‎     السبب إن الكود القديم كان يدمج كل الـ spans بسطر واحد وياخذ لون/بولد
‎     أول span بس ويطبّقه على النص المترجم كامل. الحل: نبني "runs" على
‎     مستوى الـ span (مو السطر)، وأي تغيّر لون/بولد يفتح run جديد، فيترجم
‎     ويترسم كل مقطع بلونه الأصلي بالضبط.
‎  9) كل سطر يترجم لحاله حتى لو كانت الجملة ملفوفة على سطرين: الحل إن نفس
‎     الـ runs اللي فوق تدمج الأسطر المتتالية اللي بنفس التنسيق (لون/بولد)
‎     ومالها بداية نقطة جديدة (bullet) أو فجوة رأسية كبيرة، فتترجم كوحدة
‎     وحدة (بسياق كامل) وتترسم بعدين بإعادة لف (wrap) داخل نفس صندوق
‎     الأسطر الأصلية مجتمعة، بدل ما تتقص كل نص لحاله.
‎ 10) اختفاء بعض الصور أو ظهور بقع بيضاء/زرقاء مكانها: كانت اللقطة المُركّبة
     (fix 7) تُلتقط من الموضع الأصلي وتُلصق بالموضع المعكوس، فإذا اختلفت
‎     خلفية الشريحة بين يمين وشمال ينلصق مربع بلون خلفية غلط. الحل الصحيح:
‎     نستخرج الصورة نفسها من ملف الـ PDF (extract_image) وندمج قناة
‎     الشفافية (SMask) معها فعليًا بدل الاعتماد على تصوير الخلفية، فتصير
‎     الصورة شفافة حقيقة وتتماشى مع أي خلفية بدون بقع. اللقطة المُركّبة
‎     صارت آخر fallback بس، مو الأساس.

‎ يحتاج: pip install pymupdf arabic_reshaper python-bidi flask flask-cors requests
‎ تشغيل محلي: python app.py  (يفتح على http://localhost:5000)
"""

import re
import fitz  # PyMuPDF
import arabic_reshaper
from bidi.algorithm import get_display
from flask import Flask, request, send_file, jsonify, send_from_directory
from flask_cors import CORS
import requests
import io
import os
import subprocess
import uuid
import traceback

app = Flask(__name__, static_folder='.', static_url_path='')
CORS(app)


@app.route('/')
def serve_index():
    return send_from_directory('.', 'index.html')


def _first_existing(*paths):
    """Return the first available font so the app also works without bundled fonts."""
    return next((path for path in paths if os.path.exists(path)), None)


FONT_PATH = _first_existing(
    os.path.join(os.path.dirname(__file__), "fonts", "NotoNaskhArabic-Regular.ttf"),
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
)

BOLD_FONT_PATH = _first_existing(
    os.path.join(os.path.dirname(__file__), "fonts", "NotoNaskhArabic-Bold.ttf"),
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
)

RTL_LANGS = {"ar", "ur", "fa", "he"}

BATCH_SEP = " |@| "
BATCH_CHUNK = 40

BOLD_FLAG = 2 ** 4

FULL_PAGE_IMAGE_RATIO = 0.85

BULLET_PREFIXES = ("•", "-", "–", "—", "*", "○", "▪", "➤", "◦", "✦", "➔", "★")
NUMBERED_PREFIX_RE = re.compile(r"^\d+[\.\)]\s")

IMG_BBOX_TOL = 1.5


def translate_text(text, target_lang):
    if not text.strip():
        return ""

    try:
        url = "https://translate.googleapis.com/translate_a/single"
        params = {
            "client": "gtx",
            "sl": "auto",
            "tl": target_lang,
            "dt": "t",
            "q": text,
        }

        res = requests.get(url, params=params, timeout=30)
        res.raise_for_status()

        data = res.json()
        return "".join(seg[0] for seg in data[0])

    except Exception as e:
        print("translate_text requests error:", e)

        try:
            command = [
                "curl",
                "-L",
                "-sS",
                "--max-time",
                "30",
                "--get",
                "--data-urlencode",
                "client=gtx",
                "--data-urlencode",
                "sl=auto",
                "--data-urlencode",
                f"tl={target_lang}",
                "--data-urlencode",
                "dt=t",
                "--data-urlencode",
                f"q={text}",
                url,
            ]

            raw = subprocess.check_output(
                command,
                text=True,
                stderr=subprocess.STDOUT,
            )

            data = __import__("json").loads(raw)
            return "".join(seg[0] for seg in data[0])

        except Exception as fallback_error:
            print("translate_text fallback error:", fallback_error)
            return ""


def translate_batch(texts, target_lang):
    results = [""] * len(texts)

    non_empty = [
        (i, t)
        for i, t in enumerate(texts)
        if t.strip()
    ]

    if not non_empty:
        return results

    for chunk_start in range(0, len(non_empty), BATCH_CHUNK):
        chunk = non_empty[chunk_start: chunk_start + BATCH_CHUNK]
        combined = BATCH_SEP.join(t for _, t in chunk)

        translated = translate_text(combined, target_lang)

        if not translated:
            continue

        parts = translated.split(BATCH_SEP)

        if len(parts) == len(chunk):
            for (i, _), part in zip(chunk, parts):
                results[i] = part.strip()
        else:
            print(
                f"batch split mismatch ({len(parts)} vs {len(chunk)}), "
                "falling back to individual"
            )

            for i, t in chunk:
                results[i] = translate_text(t, target_lang)

    return results


def shape_arabic(text):
    reshaped = arabic_reshaper.reshape(text)
    return get_display(reshaped)


def mirror_rect(rect, page_width):
‎    """اعكس مستطيلاً أفقياً حول محور المنتصف للصفحة."""
    return fitz.Rect(
        page_width - rect.x1,
        rect.y0,
        page_width - rect.x0,
        rect.y1,
    )


def mirror_point(pt, page_width):
‎    """اعكس نقطة واحدة أفقياً."""
    return fitz.Point(page_width - pt.x, pt.y)


def mirror_drawing_item(item, page_width):
‎    """يعكس عنصر رسم واحد."""
    kind = item[0]

    if kind == "re":
        rect = fitz.Rect(item[1])
        return ("re", mirror_rect(rect, page_width)) + tuple(item[2:])

    if kind == "l":
        return (
            "l",
            mirror_point(item[1], page_width),
            mirror_point(item[2], page_width),
        )

    if kind == "c":
        pts = item[1:5]
        return ("c",) + tuple(
            mirror_point(p, page_width)
            for p in pts
        )

    if kind == "qu":
        q = item[1]

        ul = mirror_point(q.ul, page_width)
        ur = mirror_point(q.ur, page_width)
        ll = mirror_point(q.ll, page_width)
        lr = mirror_point(q.lr, page_width)

        return ("qu", fitz.Quad(ur, ul, lr, ll))

    return item


def redraw_mirrored_drawing(page, drawing, page_width):
‎    """يعيد رسم شكل متجه واحد بموضعه المعكوس."""
    shape = page.new_shape()

    for item in drawing.get("items", []):
        mi = mirror_drawing_item(item, page_width)
        kind = mi[0]

        try:
            if kind == "re":
                shape.draw_rect(mi[1])

            elif kind == "l":
                shape.draw_line(mi[1], mi[2])

            elif kind == "c":
                shape.draw_bezier(mi[1], mi[2], mi[3], mi[4])

            elif kind == "qu":
                shape.draw_quad(mi[1])

        except Exception as e:
            print("drawing item skip:", e)

    try:
        shape.finish(
            color=drawing.get("color"),
            fill=drawing.get("fill"),
            width=drawing.get("width") or 1,
            closePath=drawing.get("closePath", True),
            even_odd=drawing.get("even_odd", False),
            dashes=drawing.get("dashes"),
        )

        shape.commit()

    except Exception as e:
        print("drawing finish/commit error:", e)


def extract_rgba_image_bytes(doc, xref):
‎    """يرجع بايتات PNG للصورة بعد دمج قناة الشفافية إذا وجدت."""
    try:
        info = doc.extract_image(xref)

    except Exception as e:
        print("extract_image failed:", e)
        return None

    if not info or not info.get("image"):
        return None

    image_bytes = info["image"]
    smask_xref = info.get("smask")

    if not smask_xref:
        return image_bytes

    try:
        base_pix = fitz.Pixmap(image_bytes)
        mask_pix = fitz.Pixmap(doc, smask_xref)

        if mask_pix.alpha:
            mask_pix = fitz.Pixmap(mask_pix, 0)

        if mask_pix.colorspace is None or mask_pix.colorspace.n != 1:
            mask_pix = fitz.Pixmap(fitz.csGRAY, mask_pix)

        if base_pix.colorspace and base_pix.colorspace.n >= 4:
            base_pix = fitz.Pixmap(fitz.csRGB, base_pix)

        combined = fitz.Pixmap(base_pix, mask_pix)
        return combined.tobytes("png")

    except Exception as e:
        print("smask combine failed, using base image without alpha:", e)
        return image_bytes


def find_xref_for_bbox(bbox, img_infos):
‎    """يطابق bbox كتلة الصورة مع قائمة الصور لجلب xref."""
    for info in img_infos:
        ibbox = fitz.Rect(info["bbox"])

        if (
            abs(ibbox.x0 - bbox.x0) < IMG_BBOX_TOL
            and abs(ibbox.y0 - bbox.y0) < IMG_BBOX_TOL
            and abs(ibbox.x1 - bbox.x1) < IMG_BBOX_TOL
            and abs(ibbox.y1 - bbox.y1) < IMG_BBOX_TOL
        ):
            return info.get("xref")

    return None


def _color_tuple(ci):
    return (
        ((ci >> 16) & 0xFF) / 255.0,
        ((ci >> 8) & 0xFF) / 255.0,
        (ci & 0xFF) / 255.0,
    )


def layout_and_draw_paragraph(
    page,
    para,
    regular_font,
    bold_font,
    bold_available,
    is_rtl,
    min_size=5,
):
‎    """يبني تدفق كلمات موحد ويرسمه داخل مساحة الفقرة."""

    def font_for(run):
        use_bold = run["bold"] and bold_available

        return (
            bold_font if use_bold else regular_font,
            BOLD_FONT_PATH if use_bold else FONT_PATH,
            "arabic-bold" if use_bold else "arabic-font",
        )

    tokens = []

    for ridx, run in enumerate(para["runs"]):
        translated = run.get("translated", "")

        if not translated:
            continue

        for word in translated.split(" "):
            if word:
                tokens.append((word, ridx))

    if not tokens:
        return

    first_dest = para["first_dest"]
    block_dest = para["block_dest"]

    max_height = para["height_budget"] * 1.3
    start_size = max(
        max(r["size"] for r in para["runs"]) - 1,
        min_size,
    )

    size = start_size

    while True:
        lines = []
        current = []
        current_width = 0.0
        avail = first_dest.width

        for word, ridx in tokens:
            font_obj, _, _ = font_for(para["runs"][ridx])

            shaped = shape_arabic(word) if is_rtl else word
            word_width = font_obj.text_length(
                shaped,
                fontsize=size,
            )

            if not current:
                current = [
                    (word, ridx, shaped, word_width)
                ]
                current_width = word_width
                continue

            space_width = font_obj.text_length(
                " ",
                fontsize=size,
            )

            if current_width + space_width + word_width <= avail:
                current.append(
                    (word, ridx, shaped, word_width)
                )
                current_width += space_width + word_width

            else:
                lines.append(current)

                current = [
                    (word, ridx, shaped, word_width)
                ]

                current_width = word_width
                avail = block_dest.width

        if current:
            lines.append(current)

        line_height = size * 1.25
        total_height = line_height * max(len(lines), 1)

        if total_height <= max_height or size <= min_size:
            break

        size -= 0.5

    y = first_dest.y0 + size

    for line_index, line_tokens in enumerate(lines):
        box = first_dest if line_index == 0 else block_dest
        cursor = box.x1 if is_rtl else box.x0
        token_count = len(line_tokens)

        for index, (word, ridx, shaped, word_width) in enumerate(line_tokens):
            run = para["runs"][ridx]

            font_obj, fontfile_used, fontname_used = font_for(run)
            color = _color_tuple(run["color"])

            if is_rtl:
                cursor -= word_width
                x = cursor
            else:
                x = cursor

            page.insert_text(
                (x, y),
                shaped,
                fontsize=size,
                fontname=fontname_used,
                fontfile=fontfile_used,
                color=color,
            )

            if is_rtl:
                if index < token_count - 1:
                    cursor -= font_obj.text_length(
                        " ",
                        fontsize=size,
                    )
            else:
                cursor += word_width

                if index < token_count - 1:
                    cursor += font_obj.text_length(
                        " ",
                        fontsize=size,
                    )

        y += line_height


def looks_like_new_bullet(text):
‎    """يتحقق هل النص بداية عنصر أو نقطة جديدة."""
    text = text.strip()

    if not text:
        return False

    if text[0] in BULLET_PREFIXES:
        return True

    return bool(NUMBERED_PREFIX_RE.match(text))


TERMINAL_PUNCT = ".!?:؛؟"
MARGIN_TOL_RATIO = 0.12


def _line_reaches_right_margin(
    line_bbox,
    block_rect,
    tol_ratio=MARGIN_TOL_RATIO,
):
    tolerance = block_rect.width * tol_ratio
    return (block_rect.x1 - line_bbox.x1) <= tolerance


def _line_starts_at_left_margin(
    line_bbox,
    block_rect,
    tol_ratio=MARGIN_TOL_RATIO,
):
    tolerance = block_rect.width * tol_ratio
    return (line_bbox.x0 - block_rect.x0) <= tolerance


def _ends_with_terminal_punct(text):
    text = text.rstrip()
    return bool(text) and text[-1] in TERMINAL_PUNCT


def _is_wrap_continuation(
    prev_line_bbox,
    prev_line_text,
    line_bbox,
    line_text,
    block_rect,
):
‎    """يحدد هل السطر استمرار للسطر السابق."""

    if prev_line_bbox is None:
        return False

    if looks_like_new_bullet(line_text):
        return False

    if _ends_with_terminal_punct(prev_line_text):
        return False

    gap = line_bbox.y0 - prev_line_bbox.y1
    typical_height = prev_line_bbox.height or 10

    if gap > typical_height * 0.6:
        return False

    if not _line_reaches_right_margin(
        prev_line_bbox,
        block_rect,
    ):
        return False

    if not _line_starts_at_left_margin(
        line_bbox,
        block_rect,
    ):
        return False

    return True


def build_paragraphs(block, page_width, is_rtl):
    block_rect = fitz.Rect(block["bbox"])

    runs = []
    current = None

    prev_line_bbox = None
    prev_line_text = ""

    for line in block["lines"]:
        spans = [
            span
            for span in line["spans"]
            if span["text"].strip()
        ]

        if not spans:
            continue

        line_bbox = fitz.Rect(line["bbox"])
        line_text = "".join(
            span["text"]
            for span in spans
        ).strip()

        is_continuation = _is_wrap_continuation(
            prev_line_bbox,
            prev_line_text,
            line_bbox,
            line_text,
            block_rect,
        )

        new_paragraph_here = not is_continuation

        for span_index, span in enumerate(spans):
            style = (
                span["color"],
                bool(span.get("flags", 0) & BOLD_FLAG),
            )

            span_rect = fitz.Rect(span["bbox"])

            if span_rect.width < 1 or span_rect.height < 1:
                continue

            starts_new_run = (
                current is None
                or style != current["style"]
                or (
                    span_index == 0
                    and new_paragraph_here
                )
            )

            if starts_new_run:
                if current is not None:
                    runs.append(current)

                current = {
                    "style": style,
                    "size": span["size"],
                    "text_parts": [],
                    "span_rects": [],
                    "new_paragraph": (
                        current is None
                        or (
                            span_index == 0
                            and new_paragraph_here
                        )
                    ),
                    "line_rect_first": line_bbox,
                    "line_rect_last": line_bbox,
                }

            current["text_parts"].append(span["text"])
            current["span_rects"].append(span_rect)
            current["size"] = max(
                current["size"],
                span["size"],
            )
            current["line_rect_last"] = line_bbox

        prev_line_bbox = line_bbox
        prev_line_text = line_text

    if current is not None:
        runs.append(current)

    paragraphs = []

    for run in runs:
        text = " ".join(
            part.strip()
            for part in run["text_parts"]
            if part.strip()
        ).strip()

        if not text:
            continue

        run_item = {
            "text": text,
            "color": run["style"][0],
            "bold": run["style"][1],
            "size": run["size"],
            "span_rects": run["span_rects"],
        }

        if run["new_paragraph"] or not paragraphs:
            paragraphs.append(
                {
                    "runs": [run_item],
                    "first_line_rect": run["line_rect_first"],
                    "last_line_rect": run["line_rect_last"],
                }
            )

        else:
            paragraph = paragraphs[-1]
            paragraph["runs"].append(run_item)
            paragraph["last_line_rect"] = run["line_rect_last"]

    items = []

    for paragraph in paragraphs:
        first_line_rect = paragraph["first_line_rect"]
        last_line_rect = paragraph["last_line_rect"]

        first_dest = (
            mirror_rect(first_line_rect, page_width)
            if is_rtl
            else first_line_rect
        )

        block_dest = (
            mirror_rect(block_rect, page_width)
            if is_rtl
            else block_rect
        )

        height_budget = max(
            last_line_rect.y1 - first_line_rect.y0,
            first_line_rect.height,
        )

        all_span_rects = [
            rect
            for run in paragraph["runs"]
            for rect in run["span_rects"]
        ]

        items.append(
            {
                "runs": paragraph["runs"],
                "first_dest": first_dest,
                "block_dest": block_dest,
                "height_budget": height_budget,
                "span_rects": all_span_rects,
            }
        )

    return items


def process_pdf(input_bytes, target_lang="ar"):
    doc = fitz.open(
        stream=input_bytes,
        filetype="pdf",
    )

    is_rtl = target_lang in RTL_LANGS

    regular_font = fitz.Font(
        fontfile=FONT_PATH,
    )

    bold_available = os.path.exists(BOLD_FONT_PATH)

    bold_font = (
        fitz.Font(fontfile=BOLD_FONT_PATH)
        if bold_available
        else regular_font
    )

    for page_num, page in enumerate(doc):
        page_width = page.rect.width

        raw_blocks = page.get_text(
            "dict",
            flags=fitz.TEXT_PRESERVE_IMAGES,
        )["blocks"]

        drawings = page.get_drawings() if is_rtl else []

        try:
            img_infos = (
                page.get_image_info(xrefs=True)
                if is_rtl
                else []
            )

        except TypeError:
            img_infos = []

        line_items = []
        image_blocks = []

        for block in raw_blocks:
            block_type = block.get("type")

            if block_type == 0:
                line_items.extend(
                    build_paragraphs(
                        block,
                        page_width,
                        is_rtl,
                    )
                )

            elif block_type == 1 and is_rtl:
                img_bytes = block.get("image")
                original_rect = fitz.Rect(block["bbox"])

                if (
                    original_rect.width < 1
                    or original_rect.height < 1
                ):
                    continue

                page_area = page.rect.width * page.rect.height
                image_area = (
                    original_rect.width
                    * original_rect.height
                )

                if (
                    page_area > 0
                    and image_area / page_area
                    > FULL_PAGE_IMAGE_RATIO
                ):
                    print(
                        f"Page {page_num + 1}: "
                        "skipping full-page background image"
                    )
                    continue

                destination_rect = mirror_rect(
                    original_rect,
                    page_width,
                )

                rgba_bytes = None

                xref = find_xref_for_bbox(
                    original_rect,
                    img_infos,
                )

                if xref:
                    rgba_bytes = extract_rgba_image_bytes(
                        doc,
                        xref,
                    )

                snapshot = None

                if not rgba_bytes:
                    try:
                        snapshot = page.get_pixmap(
                            clip=original_rect,
                            dpi=150,
                        ).tobytes("png")

                    except Exception:
                        snapshot = None

                image_blocks.append(
                    {
                        "orig": original_rect,
                        "dest": destination_rect,
                        "rgba": rgba_bytes,
                        "raw": img_bytes,
                        "snapshot": snapshot,
                    }
                )

        if not line_items and not image_blocks and not drawings:
            continue

        print(
            f"Page {page_num + 1}: "
            f"{len(line_items)} text runs, "
            f"{len(image_blocks)} images, "
            f"{len(drawings)} vector shapes → "
            f"{'mirror+' if is_rtl else ''}translate..."
        )

        flat_runs = [
            (paragraph_index, run_index, run["text"])
            for paragraph_index, paragraph in enumerate(line_items)
            for run_index, run in enumerate(paragraph["runs"])
        ]

        translations = (
            translate_batch(
                [
                    text
                    for _, _, text in flat_runs
                ],
                target_lang,
            )
            if flat_runs
            else []
        )

        for (
            paragraph_index,
            run_index,
            _,
        ), translated in zip(flat_runs, translations):
            line_items[paragraph_index]["runs"][run_index][
                "translated"
            ] = translated

        for item in line_items:
            for span_rect in item["span_rects"]:
                page.add_redact_annot(
                    span_rect,
                    fill=None,
                )

                if is_rtl:
                    mirrored_rect = mirror_rect(
                        span_rect,
                        page_width,
                    )

                    if mirrored_rect != span_rect:
                        page.add_redact_annot(
                            mirrored_rect,
                            fill=None,
                        )

        for image in image_blocks:
            page.add_redact_annot(
                image["orig"],
                fill=None,
            )

            if image["dest"] != image["orig"]:
                page.add_redact_annot(
                    image["dest"],
                    fill=None,
                )

        for drawing in drawings:
            rect = drawing.get("rect")

            if rect:
                rect = fitz.Rect(rect)

                page.add_redact_annot(
                    rect,
                    fill=None,
                )

                mirrored_rect = mirror_rect(
                    rect,
                    page_width,
                )

                if mirrored_rect != rect:
                    page.add_redact_annot(
                        mirrored_rect,
                        fill=None,
                    )

        page.apply_redactions()

        for drawing in drawings:
            redraw_mirrored_drawing(
                page,
                drawing,
                page_width,
            )

        for image in image_blocks:
            inserted = False

            for candidate in (
                image["rgba"],
                image["raw"],
                image["snapshot"],
            ):
                if not candidate:
                    continue

                try:
                    page.insert_image(
                        image["dest"],
                        stream=candidate,
                    )

                    inserted = True
                    break

                except Exception as e:
                    print(
                        "image insert attempt failed "
                        f"({e}), trying next fallback"
                    )

            if not inserted:
                print(
                    f"Page {page_num + 1}: "
                    f"could not reinsert image at "
                    f"{image['dest']} — left blank"
                )

        for paragraph in line_items:
            layout_and_draw_paragraph(
                page,
                paragraph,
                regular_font,
                bold_font,
                bold_available,
                is_rtl,
            )

        print(f"Page {page_num + 1}: done.")

    output = io.BytesIO()

    doc.save(output)
    doc.close()

    output.seek(0)
    return output


@app.route("/translate", methods=["POST"])
def translate_endpoint():
    if "file" not in request.files:
        return jsonify(
            {
                "error": "لم يتم إرفاق ملف"
            }
        ), 400

    file = request.files["file"]
    target_lang = request.form.get(
        "target_lang",
        "ar",
    )

    if not file.filename.lower().endswith(".pdf"):
        return jsonify(
            {
                "error": "الملف يجب أن يكون PDF"
            }
        ), 400

    try:
        input_bytes = file.read()

        result = process_pdf(
            input_bytes,
            target_lang,
        )

        output_name = (
            f"translated_{uuid.uuid4().hex[:8]}.pdf"
        )

        return send_file(
            result,
            mimetype="application/pdf",
            as_attachment=True,
            download_name=output_name,
        )

    except Exception as e:
        traceback.print_exc()

        return jsonify(
            {
                "error": str(e)
            }
        ), 500


@app.route("/health", methods=["GET"])
def health():
    return jsonify(
        {
            "status": "ok"
        }
    )


if __name__ == "__main__":
    port = int(
        os.environ.get(
            "PORT",
            5000,
        )
    )

    app.run(
        host="0.0.0.0",
        port=port,
        debug=False,
        use_reloader=False,
    )
```
