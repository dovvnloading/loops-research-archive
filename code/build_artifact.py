"""Assemble the dossier: compress figures, inline as data URIs, fill captions."""
import base64
import io
import json
import re
from PIL import Image

BASE = r".."

# fractal renders -> JPEG (photographic-like, compresses well); charts stay PNG
JPEG = {"m_overview": 900, "feig_zoom1": 820, "feig_zoom2": 820,
        "satellite_limb_1_9": 820, "primitive_airplane": 820, "cascade_window": 820}
PNG = ["fig_delta_light", "fig_delta_dark", "fig_rays_light", "fig_rays_dark",
       "fig_limbs_light", "fig_limbs_dark"]


def jpeg_uri(name, maxw):
    im = Image.open(rf"{BASE}\figs\{name}.png").convert("RGB")
    if im.width > maxw:
        im = im.resize((maxw, int(im.height * maxw / im.width)), Image.LANCZOS)
    buf = io.BytesIO()
    im.save(buf, "JPEG", quality=84, optimize=True)
    return "data:image/jpeg;base64," + base64.b64encode(buf.getvalue()).decode()


def png_uri(name):
    im = Image.open(rf"{BASE}\figs\{name}.png")
    if im.width > 1400:
        im = im.resize((1400, int(im.height * 1400 / im.width)), Image.LANCZOS)
    buf = io.BytesIO()
    im.save(buf, "PNG", optimize=True)
    return "data:image/png;base64," + base64.b64encode(buf.getvalue()).decode()


html = open(rf"{BASE}\template.html", encoding="utf-8").read()

for name, w in JPEG.items():
    html = html.replace(f"%%IMG_{name}%%", jpeg_uri(name, w))
for name in PNG:
    html = html.replace(f"%%IMG_{name}%%", png_uri(name))

cap = ("Limbs measured as M ∩ wake with exact ray-pair boundaries, two independent runs with opposite "
       "known biases: run A’s coarse grid inflates thin filaments (dilation halo); run B’s fine grid "
       "truncates the slow-landing wake rays at high q (chord slice — we diagnosed both and treat them as a "
       "bracket). Validation: run B reproduces the exactly-known ½-limb diameter 1.25 to 0.4%. Measured "
       "decay: q^−2.4 (A) to q^−2.8 (B) — both far below Yoccoz’s proven 1/q, hugging the conjectured 1/q². "
       "At fixed q, sizes track sin(πp/q) (at q=11: diam/sin = 0.060, 0.059, 0.057), the fine structure of the "
       "Pommerenke–Levin–Yoccoz inequality. The gap between the proven and conjectured lines is open "
       "mathematics — closed only for special families (Kapiamba 2021). A methodological footnote worth "
       "keeping: the same slow parabolic ray-landing that makes MLC hard is what limited our own measurement.")
html = html.replace("%%LIMB_CAPTION%%", cap)

leftover = re.findall(r"%%[A-Z_a-z0-9]+%%", html)
open(rf"{BASE}\dossier.html", "w", encoding="utf-8").write(html)
print("bytes:", len(html), "| unresolved placeholders:", leftover)
