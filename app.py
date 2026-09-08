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


‎# ضع هنا مسار خط عربي عادي وخط عربي Bold (نفس العائلة لو متوفر)
‎# حمّل: Noto Naskh Arabic (Regular) + Noto Naskh Arabic Bold من Google Fonts
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

‎# بت رقم 4 في span["flags"] = bold حسب توثيق PyMuPDF
BOLD_FLAG = 2 ** 4

‎# ── إصلاح ٦: أي صورة تغطي أكثر من هذي النسبة من مساحة الصفحة تُعتبر
‎# "خلفية كاملة" ونتجاهلها بالكامل (لا مسح ولا إعادة رسم) ──
FULL_PAGE_IMAGE_RATIO = 0.85

‎# ── إصلاح ٩: علامات تدل على بداية نقطة/عنصر جديد (بولت) بدل استمرار نفس السطر ──
BULLET_PREFIXES = ("•", "-", "–", "—", "*", "○", "▪", "➤", "◦", "✦", "➔", "★")
NUMBERED_PREFIX_RE = re.compile(r"^\d+[\.\)]\s")

‎# تفاوت بسيط بالبكسل عند مطابقة إحداثيات الصور (get_image_info) مع bbox الكتلة
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
                "--get", "--data-urlencode", "client=gtx",
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
‎    """اعكس مستطيلاً أفقياً حول محور المنتصف للصفحة."""
    return fitz.Rect(
        page_width - rect.x1,
        rect.y0,
        page_width - rect.x0,
        rect.y1,
    )


def mirror_point(pt, page_width):
‎    """اعكس نقطة واحدة أفقياً — نفس المبدأ المستخدم في mirror_rect بالضبط."""
    return fitz.Point(page_width - pt.x, pt.y)


‎# ───────────────────────── إصلاح ٣: عكس الأشكال المتجهية ─────────────────────
‎# هذا هو الجزء المفقود في النسخة الأصلية. السمارت آرت والرسوم التنظيمية
#
