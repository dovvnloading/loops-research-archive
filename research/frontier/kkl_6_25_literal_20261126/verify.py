"""Source identity and exact covering-model arithmetic; NOT a native proof."""
import argparse
import hashlib
import io
import json
import re
import time
from fractions import Fraction as F
from pathlib import Path
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent
SOURCES = {
    "KKL": ("2606.27272v1", 73,
            "4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140",
            {49: ["Proposition 6.23", "Lemma 6.24", "(6.25)", "(6.26)", "the maximal subwave"],
             50: ["(6.27)", "(6.28)", "(6.29)", "(6.30)", "Lemma 6.31"],
             51: ["(6.34)"], 56: ["Ideal markings"], 57: ["wave subordinate to"],
             62: ["Lemma A.10", "Lemma A.11"], 63: ["Proposition A.12"],
             64: ["Lemma A.13"], 65: ["Proposition A.14", "Lemma A.15"],
             72: ["MLC at Feigenbaum points", "[DL23b]"]}),
    "DL": ("2309.02107v3", 41,
           "e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b",
           {34: ["Lemma 5.2"], 35: ["outermost curves"]}),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def model():
    R, c, d, t = F(1, 5), F(1, 2), F(67, 40), F(7, 40)
    for k in range(2, 129):
        e = R / 2**k
        delta = e / 4
        p_left, p_right = c - R, c + R
        q_left, q_right = d - t - delta, d + t + delta
        require(0 < p_left < p_right < 1 < q_left < q_right < 2,
                "source support")
        require(0 < e <= R < 1 and 0 < t-delta < t+delta < 1,
                "radii")
        # Every endpoint inequality holds at the worst radius extremum.
        require(c-e < d-1-t-delta <= d-1-t+delta < c+e,
                "first three interlaced endpoints")
        require(c+R < d-1+t-delta, "last interlaced endpoint")
        L_left, L_right, J_right = F(1, 4), c+e/2, c+3*e/4
        require(L_left < c-R <= c-e < L_right < J_right < c+e
                <= c+R < F(3, 4), "P marked endpoints")
        require(L_left < d-1-t-delta <= d-1-t+delta < L_right
                and F(4, 5) < d-1+t-delta <= d-1+t+delta < F(9, 10),
                "Q marked endpoints")
        # Source base and source ending block, using the pulled-back cuts.
        source_end_lo, source_end_hi = L_right, 1 + J_right
        require(F(1, 4) < p_left and q_right < F(19, 10), "source base")
        require(c-e < source_end_lo < c+e <= p_right < source_end_hi,
                "source P ending: right endpoint only")
        require(source_end_lo < q_left <= d-t+delta < source_end_hi < d+t-delta,
                "source Q ending: left endpoint only")
        require(source_end_hi-source_end_lo > 1 and source_end_hi < 2,
                "source ending block covers target circle")
        require(R/e == 2**k and 1 < (t+delta)/(t-delta) <= F(15, 13),
                "width ratio")
    return {"k_min": 2, "k_max": 128, "exact_parameter_cases": 127,
            "wide_log_ratio": "2^k", "narrow_ratio_upper": "15/13",
            "scope": "rational endpoint and width-ratio arithmetic, not a native realization"}


def download(url):
    for attempt in range(3):
        try:
            with urlopen(Request(url, headers={"User-Agent": "KKL-literal-audit/1.0"}),
                         timeout=60) as response:
                return response.read()
        except OSError:
            if attempt == 2:
                raise
            time.sleep(3 * (attempt + 1))


def sources(cache):
    from pypdf import PdfReader
    out = {}
    for key, (version, count, digest, locators) in SOURCES.items():
        url = "https://arxiv.org/pdf/" + version
        local = cache / (version + ".pdf") if cache else None
        raw = local.read_bytes() if local and local.is_file() else download(url)
        require(raw.startswith(b"%PDF-"), f"{key}: not a PDF")
        actual = hashlib.sha256(raw).hexdigest()
        require(actual == digest, f"{key}: unexpected SHA-256 {actual}")
        pdf = PdfReader(io.BytesIO(raw))
        require(len(pdf.pages) == count, f"{key}: unexpected page count")
        found = {}
        for page, anchors in locators.items():
            normalized = re.sub(r"\s+", "", pdf.pages[page-1].extract_text() or "")
            for anchor in anchors:
                require(re.sub(r"\s+", "", anchor) in normalized,
                        f"{key}: missing {anchor} on page {page}")
                found[anchor] = page
        out[key] = {"version": version, "url": url, "sha256": actual,
                    "bytes": len(raw), "pages": count, "locators": found}
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model-only", action="store_true")
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--output", type=Path, default=HERE / "source_lock.json")
    args = parser.parse_args()
    result = {"schema": 1, "scope": "source identity and elementary model arithmetic only",
              "model": model()}
    if not args.model_only:
        result["sources"] = sources(args.cache)
    rendered = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if not args.model_only:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
