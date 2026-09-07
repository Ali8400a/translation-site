"""
باك إند ترجمة ملفات PDF - يستبدل النص الإنجليزي فعلياً بالعربي داخل بنية الملف

نسخة معدّلة تحل:
  1) اختفاء البولد (كان يأخذ التنسيق من أول span بس ويهمل flags)
  2) تراكب الأيقونات فوق النص (كان يرسم الصور بعد النص دايمًا)
  3) انكسار السمارت آرت (كان يعكس النص والصور بس، ويترك الأشكال المتجهية
     [مربعات/أسهم/خطوط الرسم التنظيمي] بمكانها الأصلية)
  4) اختفاء صور الخلفية عند فشل إعادة الإدراج (كان يمسح صمت بدون fallback)
  5) فيضان النص خارج حدود صندوقه (كان يرسم بحجم خط ثابت بدون تحقق من العرض)
  6) خلفيات شرائح الفواصل الكاملة تختفي (تُترك بحالها الآن، بدون مسح ولا إعادة رسم)
  7) مربع أسود مكان أيقونة الدبوس الشفافة (اللقطة المُركّبة صارت الأساس، مو fallback،
     لأن البايتات الخام تفقد الشفافية بصمت بدون Exception)

  ── إصلاحات جديدة (الجولة الثانية) ──
  8) الهايلايت/اللون يطلع على السطر كامل بدل الكلمة صاحبة اللون فعليًا:
     السبب إن الكود القديم كان يدمج كل الـ spans بسطر واحد وياخذ لون/بولد
     أول span بس ويطبّقه على النص المترجم كامل. الحل: نبني "runs" على
     مستوى الـ span (مو السطر)، وأي تغيّر لون/بولد يفتح run جديد، فيترجم
     ويترسم كل مقطع بلونه الأصلي بالضبط.
  9) كل سطر يترجم لحاله حتى لو كانت الجملة ملفوفة على سطرين: الحل إن نفس
     الـ runs اللي فوق تدمج الأسطر المتتالية اللي بنفس التنسيق (لون/بولد)
     ومالها بداية نقطة جديدة (bullet) أو فجوة رأسية كبيرة، فتترجم كوحدة
     وحدة (بسياق كامل) وتترسم بعدين بإعادة لف (wrap) داخل نفس صندوق
     الأسطر الأصلية مجتمعة، بدل ما تتقص كل نص لحاله.
 10) اختفاء بعض الصور أو ظهور بقع بيضاء/زرقاء مكانها: كانت اللقطة المُركّبة
     (fix 7) تُلتقط من الموضع الأصلي وتُلصق بالموضع المعكوس، فإذا اختلفت
     خلفية الشريحة بين يمين وشمال ينلصق مربع بلون خلفية غلط. الحل الصحيح:
     نستخرج الصورة نفسها من ملف الـ PDF (extract_image) وندمج قناة
     الشفافية (SMask) معها فعليًا بدل الاعتماد على تصوير الخلفية، فتصير
     الصورة شفافة حقيقة وتتماشى مع أي خلفية بدون بقع. اللقطة المُركّبة
     صارت آخر fallback بس، مو الأساس.

يحتاج: pip install pymupdf arabic_reshaper python-bidi flask flask-cors requests
تشغيل محلي: python app.py  (يفتح على http://localhost:5000)
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


# ضع هنا مسار خط عربي عادي وخط عربي Bold (نفس العائلة لو متوفر)
# حمّل: Noto Naskh Arabic (Regular) + Noto Naskh Arabic Bold من Google Fonts
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

# بت رقم 4 في span["flags"] = bold حسب توثيق PyMuPDF
BOLD_FLAG = 2 ** 4

# ── إصلاح ٦: أي صورة تغطي أكثر من هذي النسبة من مساحة الصفحة تُعتبر
# "خلفية كاملة" ونتجاهلها بالكامل (لا مسح ولا إعادة رسم) ──
FULL_PAGE_IMAGE_RATIO = 0.85

# ── إصلاح ٩: علامات تدل على بداية نقطة/عنصر جديد (بولت) بدل استمرار نفس السطر ──
BULLET_PREFIXES = ("•", "-", "–", "—", "*", "○", "▪", "➤", "◦", "✦", "➔", "★")
NUMBERED_PREFIX_RE = re.compile(r"^\d+[\.\)]\s")

# تفاوت بسيط بالبكسل عند مطابقة إحداثيات الصور (get_image_info) مع bbox الكتلة
IMG_BBOX_TOL = 1.5


def translate_text(text, target_lang):
    if not text.strip():
        return ""
    try:
        url = "https://translate.googleapis.com/translate_a/single"
        params = {"client": "gtx", "sl": "auto", "tl": target_lang, "dt": "t", "q": text}
        res = requests.get(url, params=params, timeout=30)
        res.raise_for_status()
        data = res.json()
        return "".join(seg[0] for seg in data[0])
    except Exception as e:
        # Some hosted environments rate-limit Python's HTTP fingerprint while
        # allowing the same public endpoint through curl. Keep the normal
        # requests path first, then use curl as a narrow compatibility fallback.
        print("translate_text requests error:", e)
        try:
            command = [
                "curl", "-L", "-sS", "--max-time", "30",
                "--get", "--data-urlencode", f"client=gtx",
                "--data-urlencode", "sl=auto",
                "--data-urlencode", f"tl={target_lang}",
                "--data-urlencode", "dt=t",
                "--data-urlencode", f"q={text}",
                url,
            ]
            raw = subprocess.check_output(command, text=True, stderr=subprocess.STDOUT)
            data = __import__("json").loads(raw)
            return "".join(seg[0] for seg in data[0])
        except Exception as fallback_error:
            print("translate_text fallback error:", fallback_error)
            return ""


def translate_batch(texts, target_lang):
    results = [""] * len(texts)
    non_empty = [(i, t) for i, t in enumerate(texts) if t.strip()]
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
            print(f"batch split mismatch ({len(parts)} vs {len(chunk)}), falling back to individual")
            for i, t in chunk:
                results[i] = translate_text(t, target_lang)
    return results


def shape_arabic(text):
    reshaped = arabic_reshaper.reshape(text)
    return get_display(reshaped)


def mirror_rect(rect, page_width):
    """اعكس مستطيلاً أفقياً حول محور المنتصف للصفحة."""
    return fitz.Rect(
        page_width - rect.x1,
        rect.y0,
        page_width - rect.x0,
        rect.y1,
    )


def mirror_point(pt, page_width):
    """اعكس نقطة واحدة أفقياً — نفس المبدأ المستخدم في mirror_rect بالضبط."""
    return fitz.Point(page_width - pt.x, pt.y)


# ───────────────────────── إصلاح ٣: عكس الأشكال المتجهية ─────────────────────
# هذا هو الجزء المفقود في النسخة الأصلية. السمارت آرت والرسوم التنظيمية
# مبنية من أشكال متجهية (مربعات/خطوط/أسهم) — لازم تنعكس بنفس معادلة النص
# وإلا يصير النص بمكان معكوس والصندوق بمكانه القديم = تراكب فوضوي.

def mirror_drawing_item(item, page_width):
    """يعكس عنصر رسم واحد (سطر من page.get_drawings()['items'])."""
    kind = item[0]
    if kind == "re":
        rect = fitz.Rect(item[1])
        return ("re", mirror_rect(rect, page_width)) + tuple(item[2:])
    if kind == "l":
        return ("l", mirror_point(item[1], page_width), mirror_point(item[2], page_width))
    if kind == "c":
        pts = item[1:5]
        return ("c",) + tuple(mirror_point(p, page_width) for p in pts)
    if kind == "qu":
        q = item[1]
        ul, ur = mirror_point(q.ul, page_width), mirror_point(q.ur, page_width)
        ll, lr = mirror_point(q.ll, page_width), mirror_point(q.lr, page_width)
        # عند العكس الأفقي يتبادل اليسار مع اليمين
        return ("qu", fitz.Quad(ur, ul, lr, ll))
    return item  # نوع غير متوقع — نتركه كما هو بدل ما نكسره


def redraw_mirrored_drawing(page, drawing, page_width):
    """يعيد رسم شكل متجه واحد (مربع/سهم/خط من السمارت آرت) بموضعه المعكوس
    مع نفس اللون والتعبئة وسمك الخط الأصلي."""
    shape = page.new_shape()
    for item in drawing.get("items", []):
        mi = mirror_drawing_item(item, page_width)
        k = mi[0]
        try:
            if k == "re":
                shape.draw_rect(mi[1])
            elif k == "l":
                shape.draw_line(mi[1], mi[2])
            elif k == "c":
                shape.draw_bezier(mi[1], mi[2], mi[3], mi[4])
            elif k == "qu":
                shape.draw_quad(mi[1])
        except Exception as e:
            print("  drawing item skip:", e)
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
        print("  drawing finish/commit error:", e)


# ───────────────────────── إصلاح ١٠: استخراج الصور بشفافيتها الحقيقية ─────────
# بدل الاعتماد على "لقطة" من خلفية الموضع الأصلي (اللي تسبب بقع بلون غلط لما
# تختلف خلفية الموضع الأصلي عن المعكوس)، نستخرج الصورة من الـ PDF مباشرة وندمج
# قناة الشفافية (SMask) الحقيقية فيها، فتصير صورة PNG شفافة فعلاً تتماشى مع
# أي خلفية تنحط فوقها بدون أي بقعة.

def extract_rgba_image_bytes(doc, xref):
    """يرجع بايتات PNG للصورة (xref) بعد دمج SMask فيها إذا موجودة.
    يرجع None لو فشل الاستخراج بالكامل."""
    try:
        info = doc.extract_image(xref)
    except Exception as e:
        print("  extract_image failed:", e)
        return None
    if not info or not info.get("image"):
        return None

    image_bytes = info["image"]
    smask_xref = info.get("smask")
    if not smask_xref:
        return image_bytes  # ما فيها قناة شفافية أصلاً، رجّعها كما هي

    try:
        base_pix = fitz.Pixmap(image_bytes)
        mask_pix = fitz.Pixmap(doc, smask_xref)
        # قناة القناع لازم تكون رمادية بدون ألفا قبل الدمج
        if mask_pix.alpha:
            mask_pix = fitz.Pixmap(mask_pix, 0)
        if mask_pix.colorspace is None or mask_pix.colorspace.n != 1:
            mask_pix = fitz.Pixmap(fitz.csGRAY, mask_pix)
        if base_pix.colorspace and base_pix.colorspace.n >= 4:
            # CMYK مثلاً — حوّلها RGB قبل إضافة الألفا
            base_pix = fitz.Pixmap(fitz.csRGB, base_pix)
        combined = fitz.Pixmap(base_pix, mask_pix)
        return combined.tobytes("png")
    except Exception as e:
        print("  smask combine failed, using base image without alpha:", e)
        return image_bytes


def find_xref_for_bbox(bbox, img_infos):
    """يطابق bbox كتلة الصورة (من get_text) مع قائمة get_image_info لجلب الـ xref."""
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


# ───────────────────────── إصلاح ١٢: الكلمة الملوّنة تبان "منفصلة" بفجوة ─────
# بعد حل التراكب، ظهرت مشكلة ثانية: الكلمة الملوّنة (زي "الإصابة:") والنص
# العادي بعدها كانا يترسمان كـ"صندوقين" مستقلين، كل وحدة بمقاسها الأصلي
# (الإنجليزي) الخاص فيها. بما إن طول الترجمة العربية يختلف عن الكلمة
# الإنجليزية الأصلية، يطلع بينهم فراغ غير منتظم أو تراكب خفيف، ويبان الكلام
# الملوّن كأنه جملة منفصلة تمامًا بدل ما يكون مجرد تلوين داخل نفس الجملة.
#
# الحل الجذري: بدل ما نرسم كل run (مقطع بلون/تنسيق واحد) في صندوقه الخاص،
# نجمع كل الـ runs اللي بنفس "الفقرة" (نفس الجملة/العنصر، حتى لو فيها أكثر
# من لون) في تدفّق نصي واحد على مستوى الكلمة: كل كلمة تترسم مباشرة بعد اللي
# قبلها (بمسافة عادية بس)، ولون/تنسيق كل كلمة يجي من الـ run الأصلي التابعة
# له. هذا يخلي الفقرة تبان جملة وحدة متصلة طبيعية، والتلوين مجرد تمييز
# بصري داخلها — بالضبط زي ما يكون بالأصل الإنجليزي.

def _color_tuple(ci):
    return (
        ((ci >> 16) & 0xFF) / 255.0,
        ((ci >> 8) & 0xFF) / 255.0,
        (ci & 0xFF) / 255.0,
    )


def layout_and_draw_paragraph(page, para, regular_font, bold_font, bold_available,
                               is_rtl, min_size=5):
    """يبني تدفّق كلمات موحّد لكل الـ runs بفقرة وحدة، يلفّه داخل صندوقها
    (أول سطر بعرضه الفعلي، وباقي الأسطر بعرض صندوق النص الكامل)، ويرسمه
    كلمة-كلمة بحيث تلتصق الكلمات ببعض بمسافة عادية بس بغض النظر عن اختلاف
    طول كل جزء عن أصله الإنجليزي."""

    def font_for(run):
        use_bold = run["bold"] and bold_available
        return (
            bold_font if use_bold else regular_font,
            BOLD_FONT_PATH if use_bold else FONT_PATH,
            "arabic-bold" if use_bold else "arabic-font",
        )

    # ابني تدفّق التوكنز (كلمة + فهرس الـ run التابعة له) بترتيبها المنطقي
    tokens = []  # (word, run_index)
    for ridx, run in enumerate(para["runs"]):
        translated = run.get("translated", "")
        if not translated:
            continue
        for w in translated.split(" "):
            if w:
                tokens.append((w, ridx))
    if not tokens:
        return

    first_dest = para["first_dest"]
    block_dest = para["block_dest"]
    max_height = para["height_budget"] * 1.3
    start_size = max(max(r["size"] for r in para["runs"]) - 1, min_size)

    size = start_size
    while True:
        lines = []          # كل عنصر: قائمة (word, ridx, shaped, width)
        current = []
        current_width = 0.0
        avail = first_dest.width

        for word, ridx in tokens:
            font_obj, _, _ = font_for(para["runs"][ridx])
            shaped = shape_arabic(word) if is_rtl else word
            w_width = font_obj.text_length(shaped, fontsize=size)

            if not current:
                current = [(word, ridx, shaped, w_width)]
                current_width = w_width
                continue

            space_width = font_obj.text_length(" ", fontsize=size)
            if current_width + space_width + w_width <= avail:
                current.append((word, ridx, shaped, w_width))
                current_width += space_width + w_width
            else:
                lines.append(current)
                current = [(word, ridx, shaped, w_width)]
                current_width = w_width
                avail = block_dest.width  # أي سطر بعد الأول ياخذ عرض الصندوق كامل

        if current:
            lines.append(current)

        line_height = size * 1.25
        total_height = line_height * max(len(lines), 1)
        if total_height <= max_height or size <= min_size:
            break
        size -= 0.5

    # ─── الرسم الفعلي: كلمة كلمة، كل وحدة بلونها/تنسيقها الأصلي، بدون أي
    # فراغ زايد بينها — تلتصق ببعض بمسافة عادية بس زي جملة طبيعية. ──
    y = first_dest.y0 + size
    for li, line_tokens in enumerate(lines):
        box = first_dest if li == 0 else block_dest
        cursor = box.x1 if is_rtl else box.x0
        n = len(line_tokens)
        for i, (word, ridx, shaped, w_width) in enumerate(line_tokens):
            run = para["runs"][ridx]
            font_obj, fontfile_used, fontname_used = font_for(run)
            color = _color_tuple(run["color"])

            if is_rtl:
                cursor -= w_width
                x = cursor
            else:
                x = cursor

            page.insert_text(
                (x, y), shaped,
                fontsize=size, fontname=fontname_used,
                fontfile=fontfile_used, color=color,
            )

            if is_rtl:
                if i < n - 1:
                    cursor -= font_obj.text_length(" ", fontsize=size)
            else:
                cursor += w_width
                if i < n - 1:
                    cursor += font_obj.text_length(" ", fontsize=size)
        y += line_height


def looks_like_new_bullet(text):
    """يحاول يكتشف إذا كان سطر جديد هو بداية عنصر/نقطة جديدة (بدل استمرار
    نفس الجملة الملفوفة) عشان ما ندمج عنصرين مختلفين بنقطة وحدة."""
    t = text.strip()
    if not t:
        return False
    if t[0] in BULLET_PREFIXES:
        return True
    return bool(NUMBERED_PREFIX_RE.match(t))


TERMINAL_PUNCT = ".!?:؛؟"

# نسبة تسامح (من عرض الكتلة) لما نتحقق هل سطر "يلامس" حافة الصندوق اليمين/اليسار
MARGIN_TOL_RATIO = 0.12


def _line_reaches_right_margin(line_bbox, block_rect, tol_ratio=MARGIN_TOL_RATIO):
    tol = block_rect.width * tol_ratio
    return (block_rect.x1 - line_bbox.x1) <= tol


def _line_starts_at_left_margin(line_bbox, block_rect, tol_ratio=MARGIN_TOL_RATIO):
    tol = block_rect.width * tol_ratio
    return (line_bbox.x0 - block_rect.x0) <= tol


def _ends_with_terminal_punct(text):
    t = text.rstrip()
    return bool(t) and t[-1] in TERMINAL_PUNCT


def _is_wrap_continuation(prev_line_bbox, prev_line_text, line_bbox, line_text, block_rect):
    """يقرر هل السطر الحالي هو فعلاً استمرار (wrap) لنفس جملة السطر اللي قبله،
    أو سطر مستقل تم رصّه تحته قصدًا (زي عنوان بثلاث أسطر منفصلة).

    نطلب توفر *كل* هذي الشروط قبل الدمج (تحفّظ مقصود؛ عدم الدمج أسلم من دمج
    غلط، لأن الدمج الغلط يسبب تصادم نص فوق نص أو خلط جمل غير مرتبطة):
      - فجوة رأسية صغيرة (تباعد سطر عادي، مو فقرة جديدة).
      - السطر اللي قبل ما ينتهي بعلامة ترقيم تدل على نهاية جملة/عنصر.
      - السطر اللي قبل يوصل تقريبًا لحافة الصندوق اليمين (دليل إنه انلف
        بسبب ضيق المساحة، مو سطر قصير مقصود لحاله زي عنوان متوسّط).
      - السطر الحالي يبدأ تقريبًا من حافة الصندوق الشمال (استمرار طبيعي
        لالتفاف نص، مو نص متوسّط له إزاحة مختلفة عن باقي الأسطر).
      - السطر الحالي مو بداية نقطة/بولت جديدة.
    """
    if prev_line_bbox is None:
        return False
    if looks_like_new_bullet(line_text):
        return False
    if _ends_with_terminal_punct(prev_line_text):
        return False

    gap = line_bbox.y0 - prev_line_bbox.y1
    typical_h = prev_line_bbox.height or 10
    if gap > typical_h * 0.6:
        return False

    if not _line_reaches_right_margin(prev_line_bbox, block_rect):
        return False
    if not _line_starts_at_left_margin(line_bbox, block_rect):
        return False

    return True


# ───────────────────────── إصلاح ٨ و ٩ و ١٢: بناء فقرات (paragraphs) ─────────
# بدل ما نترجم كل سطر PyMuPDF لحاله (ونطبّق لون أول span بس على السطر كامل)،
# نبني "فقرات": كل فقرة = جملة/عنصر واحد قد يحتوي أكثر من run (لون/تنسيق
# مختلف)، وقد يمتد على أكثر من سطر أصلي واحد (wrap). كل الـ runs بنفس
# الفقرة تترسم بعدين كتدفّق كلمات واحد متلاصق (شوف layout_and_draw_paragraph)
# عشان الكلمة الملوّنة تبان جزء طبيعي من نفس الجملة، مو منفصلة عنها.

def build_paragraphs(block, page_width, is_rtl):
    block_rect = fitz.Rect(block["bbox"])
    runs = []
    current = None
    prev_line_bbox = None
    prev_line_text = ""

    for line in block["lines"]:
        spans = [s for s in line["spans"] if s["text"].strip()]
        if not spans:
            continue

        line_bbox = fitz.Rect(line["bbox"])
        line_text = "".join(s["text"] for s in spans).strip()

        is_continuation = _is_wrap_continuation(
            prev_line_bbox, prev_line_text, line_bbox, line_text, block_rect
        )
        new_paragraph_here = not is_continuation

        for si, s in enumerate(spans):
            style = (s["color"], bool(s.get("flags", 0) & BOLD_FLAG))
            span_rect = fitz.Rect(s["bbox"])
            if span_rect.width < 1 or span_rect.height < 1:
                continue

            starts_new_run = (
                current is None
                or style != current["style"]
                or (si == 0 and new_paragraph_here)
            )
            if starts_new_run:
                if current is not None:
                    runs.append(current)
                current = {
                    "style": style,
                    "size": s["size"],
                    "text_parts": [],
                    "span_rects": [],
                    # فقرة جديدة تبدأ بس لو هذا أول run بالكتلة كلها، أو
                    # جانا تحديد صريح إن السطر مو استمرار لللي قبله
                    "new_paragraph": (current is None) or (si == 0 and new_paragraph_here),
                    "line_rect_first": line_bbox,
                    "line_rect_last": line_bbox,
                }
            current["text_parts"].append(s["text"])
            current["span_rects"].append(span_rect)
            current["size"] = max(current["size"], s["size"])
            current["line_rect_last"] = line_bbox

        prev_line_bbox = line_bbox
        prev_line_text = line_text

    if current is not None:
        runs.append(current)

    # جمّع الـ runs المتتالية بفقرات: run معلّم new_paragraph=True يبدأ فقرة جديدة
    paragraphs = []
    for r in runs:
        text = " ".join(p.strip() for p in r["text_parts"] if p.strip()).strip()
        if not text:
            continue
        run_item = {
            "text": text,
            "color": r["style"][0],
            "bold": r["style"][1],
            "size": r["size"],
            "span_rects": r["span_rects"],
        }
        if r["new_paragraph"] or not paragraphs:
            paragraphs.append({
                "runs": [run_item],
                "first_line_rect": r["line_rect_first"],
                "last_line_rect": r["line_rect_last"],
            })
        else:
            para = paragraphs[-1]
            para["runs"].append(run_item)
            para["last_line_rect"] = r["line_rect_last"]

    items = []
    for para in paragraphs:
        first_line_rect = para["first_line_rect"]
        last_line_rect = para["last_line_rect"]
        first_dest = mirror_rect(first_line_rect, page_width) if is_rtl else first_line_rect
        block_dest = mirror_rect(block_rect, page_width) if is_rtl else block_rect
        height_budget = max(last_line_rect.y1 - first_line_rect.y0, first_line_rect.height)
        all_span_rects = [rect for run in para["runs"] for rect in run["span_rects"]]
        items.append({
            "runs": para["runs"],          # كل run فيها: text/color/bold/size/span_rects
            "first_dest": first_dest,      # مكان أول سطر أصلي بهذي الفقرة
            "block_dest": block_dest,      # عرض صندوق النص الكامل (لأي سطر زيادة)
            "height_budget": height_budget,
            "span_rects": all_span_rects,  # كل الـ spans بالفقرة (للمسح الدقيق)
        })
    return items


def process_pdf(input_bytes, target_lang="ar"):
    doc = fitz.open(stream=input_bytes, filetype="pdf")
    is_rtl = target_lang in RTL_LANGS

    regular_font = fitz.Font(fontfile=FONT_PATH)
    bold_available = os.path.exists(BOLD_FONT_PATH)
    bold_font = fitz.Font(fontfile=BOLD_FONT_PATH) if bold_available else regular_font

    for page_num, page in enumerate(doc):
        pw = page.rect.width

        raw_blocks = page.get_text("dict", flags=fitz.TEXT_PRESERVE_IMAGES)["blocks"]
        # نلتقط الأشكال المتجهية (مربعات/أسهم/خطوط) قبل أي تعديل على الصفحة
        drawings = page.get_drawings() if is_rtl else []
        # قائمة الصور الحقيقية مع الـ xref الخاص فيها (لإصلاح ١٠) — قبل أي تعديل
        try:
            img_infos = page.get_image_info(xrefs=True) if is_rtl else []
        except TypeError:
            # نسخ قديمة من PyMuPDF ما فيها معامل xrefs
            img_infos = []

        line_items = []
        image_blocks = []

        for block in raw_blocks:
            btype = block.get("type")

            if btype == 0:  # نص
                # ── إصلاح ٨ و ٩ و ١٢: نبني فقرات (جملة/عنصر قد يحوي أكثر من
                # لون) بدل دمج السطر كامل أو معاملة كل run كصندوق مستقل ──
                line_items.extend(build_paragraphs(block, pw, is_rtl))

            elif btype == 1 and is_rtl:  # صورة
                img_bytes = block.get("image")
                orig = fitz.Rect(block["bbox"])
                if orig.width < 1 or orig.height < 1:
                    continue

                # ── إصلاح ٦: خلفيات الفواصل الكاملة (تغطي أغلب الصفحة) ──
                # نتجاهلها تماماً: لا مسح ولا إعادة رسم. هذي الصور غالباً
                # صور خلفية كبيرة، وأي محاولة تحريكها/إعادة إدراجها تفشل
                # بصمت وتسيب مربع أبيض فاضي مكانها. تركها بحالها أضمن حل.
                page_area = page.rect.width * page.rect.height
                img_area = orig.width * orig.height
                if page_area > 0 and (img_area / page_area) > FULL_PAGE_IMAGE_RATIO:
                    print(f"  Page {page_num+1}: skipping full-page background image (untouched)")
                    continue

                dest = mirror_rect(orig, pw)

                # ── إصلاح ١٠: نحاول أولاً نستخرج الصورة الحقيقية من الـ PDF
                # وندمج شفافيتها (SMask) بدل الاعتماد على لقطة الخلفية، اللي
                # تسبب بقع بلون غلط لو اختلفت خلفية الموضع الأصلي عن المعكوس.
                rgba_bytes = None
                xref = find_xref_for_bbox(orig, img_infos)
                if xref:
                    rgba_bytes = extract_rgba_image_bytes(doc, xref)

                # لقطة مُركّبة من العرض الفعلي كـ fallback أخير بس (مو أساس)،
                # تُستخدم فقط لو فشل استخراج الصورة الحقيقية بشفافيتها.
                snapshot = None
                if not rgba_bytes:
                    try:
                        snapshot = page.get_pixmap(clip=orig, dpi=150).tobytes("png")
                    except Exception:
                        snapshot = None

                image_blocks.append({
                    "orig": orig, "dest": dest,
                    "rgba": rgba_bytes,
                    "raw": img_bytes,
                    "snapshot": snapshot,
                })

        if not line_items and not image_blocks and not drawings:
            continue

        print(
            f"Page {page_num+1}: {len(line_items)} text runs, {len(image_blocks)} images, "
            f"{len(drawings)} vector shapes → {'mirror+' if is_rtl else ''}translate..."
        )

        # كل فقرة ممكن تحوي أكثر من run (لون/تنسيق مختلف) — نترجم كل run
        # لحاله (يحافظ على حدود التلوين)، بس نجمعهم بطلب ترجمة واحد للصفحة
        flat_runs = [(pi, ri, run["text"])
                     for pi, para in enumerate(line_items)
                     for ri, run in enumerate(para["runs"])]

        translations = (
            translate_batch([t for _, _, t in flat_runs], target_lang)
            if flat_runs else []
        )
        for (pi, ri, _), translated in zip(flat_runs, translations):
            line_items[pi]["runs"][ri]["translated"] = translated

        # ─── مسح كل شي: نص + صور + أشكال متجهية (أصلي ووجهته المعكوسة) ────────
        # ── إصلاح ١١: نمسح كل span لحاله بدقة، مو صندوق union كبير قد يبلع
        # مساحة مقطع مجاور (زي كلمة بولد بنفس السطر) ويسبب مسح/تراكب غلط.
        for l in line_items:
            for span_rect in l["span_rects"]:
                page.add_redact_annot(span_rect, fill=None)
                if is_rtl:
                    mr = mirror_rect(span_rect, pw)
                    if mr != span_rect:
                        page.add_redact_annot(mr, fill=None)
        for b in image_blocks:
            page.add_redact_annot(b["orig"], fill=None)
            if b["dest"] != b["orig"]:
                page.add_redact_annot(b["dest"], fill=None)
        for d in drawings:
            r = d.get("rect")
            if r:
                page.add_redact_annot(fitz.Rect(r), fill=None)
                mr = mirror_rect(fitz.Rect(r), pw)
                if mr != fitz.Rect(r):
                    page.add_redact_annot(mr, fill=None)

        page.apply_redactions()

        # ─── إعادة الرسم بالترتيب: أشكال متجهية أولاً (خلفية) ثم صور ثم نص فوق
        # هذا الترتيب يضمن إن النص يبقى مقروء فوق أي تراكب طفيف متبقي،
        # عكس النسخة الأصلية اللي كانت ترسم الصور آخر شي فتغطي النص. ──

        # ١) الأشكال المتجهية المعكوسة (مربعات/أسهم السمارت آرت)
        for d in drawings:
            redraw_mirrored_drawing(page, d, pw)

        # ٢) الصور (أيقونات/شعارات) بموضعها المعكوس
        # الأولوية: الصورة الحقيقية المُدمجة مع شفافيتها → البايتات الخام →
        # لقطة الخلفية (أضعف خيار، آخر حل لو الباقي فشل).
        for b in image_blocks:
            inserted = False
            for candidate in (b["rgba"], b["raw"], b["snapshot"]):
                if not candidate:
                    continue
                try:
                    page.insert_image(b["dest"], stream=candidate)
                    inserted = True
                    break
                except Exception as e:
                    print(f"  image insert attempt failed ({e}), trying next fallback")
            if not inserted:
                print(f"  Page {page_num+1}: could not reinsert image at {b['dest']} — left blank")

        # ٣) النص المترجم فوق الكل — كل فقرة تترسم كتدفّق كلمات واحد متلاصق
        # (إصلاح ١٢)، بدل ما يترسم كل run بصندوقه المستقل.
        for para in line_items:
            layout_and_draw_paragraph(
                page, para, regular_font, bold_font, bold_available, is_rtl,
            )

        print(f"Page {page_num+1}: done.")

    out = io.BytesIO()
    doc.save(out)
    doc.close()
    out.seek(0)
    return out


@app.route("/translate", methods=["POST"])
def translate_endpoint():
    if "file" not in request.files:
        return jsonify({"error": "لم يتم إرفاق ملف"}), 400

    file = request.files["file"]
    target_lang = request.form.get("target_lang", "ar")

    if not file.filename.lower().endswith(".pdf"):
        return jsonify({"error": "الملف يجب أن يكون PDF"}), 400

    try:
        input_bytes = file.read()
        result = process_pdf(input_bytes, target_lang)
        out_name = f"translated_{uuid.uuid4().hex[:8]}.pdf"
        return send_file(
            result,
            mimetype="application/pdf",
            as_attachment=True,
            download_name=out_name,
        )
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


@app.route("/health", methods=["GET"])
def health():
    return jsonify({"status": "ok"})


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="127.0.0.1", port=port, debug=False, use_reloader=False)
