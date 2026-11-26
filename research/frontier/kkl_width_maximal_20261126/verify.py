"""Exact endpoint/selection diagnostics and pinned PDF identity, not proof checking."""
import argparse
import hashlib
import io
import itertools
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
            {49: ["Proposition 6.23", "Lemma 6.24", "(6.25)", "(6.26)",
                  "the maximal subwave"],
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


def endpoints(d, r, h):
    # Closed ranges of left and right endpoints for every radius in [r,h*r].
    return ((d-h*r, d-r), (d+r, d+h*r))


def model():
    c, h, r0 = F(1, 2), F(5, 4), F(1, 10)
    k_max = 128
    radii = [r0 / 4**i for i in range(k_max)]
    packets = []
    for r in radii:
        P, Q = endpoints(c, r, h), endpoints(c+r/2, r, h)
        pL, pR = P
        qL, qR = Q
        # Uniform strict interlacing (all radii, not samples).
        require(pL[1] < qL[0] and qL[1] < pR[0] and pR[1] < qR[0],
                "same-scale interlacing")
        require((h-1)*r < r/2 < 2*r and h*r < 1, "circle intersection")
        require(F(1, 4) < pL[0] <= pR[1] < 1 < 1+qL[0]
                <= 1+qR[1] < F(7, 4) < 2, "source base and sheets")
        require(h*r/r == h > 1, "constant log width ratio")
        packets.append((P, Q))
    # Every smaller disk lies strictly within every larger disk in projection.
    # Same-sheet sector supports are therefore disjoint, too.
    comparisons = 0
    for i, big in enumerate(packets):
        for small in packets[i+1:]:
            for (bigL, bigR), (smallL, smallR) in itertools.product(big, small):
                require(bigL[1] < smallL[0] and smallR[1] < bigR[0],
                        "distinct-scale strict disk inclusion")
                comparisons += 1
    marking_cases = 0
    for k in range(1, k_max+1):
        e = radii[k-1]
        L0, L1, J1, R1 = F(1, 4), c+e/2, c+3*e/4, F(3, 4)
        require(0 < L0 < L1 < J1 < R1 < 1, "ordered target cuts")
        E0, E1 = L1, 1+J1
        require(1 < E1-E0 < 2 and E1 < 2, "degree two ending block")
        for P, Q in packets[:k]:
            for left, right in (P, Q):
                require(L0 < left[0] <= left[1] < L1 < J1
                        < right[0] <= right[1] < R1, "target marks and common J")
            pL, pR = P
            qL, qR = Q
            require(pL[1] < E0 < pR[0] <= pR[1] < E1,
                    "P right endpoint in E only")
            require(E0 < 1+qL[0] <= 1+qL[1] < E1 < 1+qR[0],
                    "Q left endpoint in E only")
            require(pR[1] < 1+qL[0], "no common source bounded-side interval")
            marking_cases += 1
    # Enumerate the independent-pair conflict graph. Weights are exact integer
    # multiples of the positive analytic packet width log(5/4)/pi.
    # Full-packet combinatorics only; NOTE proves the arbitrary subfamily bound.
    mask_count = 0
    for k in range(1, 9):
        maximum, maximizers = -1, 0
        for mask in range(1 << (2*k)):
            mask_count += 1
            if any((mask >> (2*i)) & 3 == 3 for i in range(k)):
                continue
            count = mask.bit_count()
            require(count <= k and 2*k-count >= k, "selection and discard bound")
            if count > maximum:
                maximum, maximizers = count, 1
            elif count == maximum:
                maximizers += 1
        require(maximum == k and maximizers == 2**k, "attainment and count")
    return {
        "k_min": 1, "k_max": k_max, "same_scale_cases": k_max,
        "distinct_scale_pair_comparisons": comparisons,
        "marking_packet_cases": marking_cases,
        "enumerated_masks": mask_count, "mask_horizon_max": 8,
        "radius_ratio": "5/4", "scale_ratio": "1/4",
        "source_width_units": "2*k", "maximum_width_units": "k",
        "discard_lower_bound_units": "k", "units": "log(5/4)/pi",
        "scope": "rational extrema and finite conflict graph only; not a native realization",
    }


def download(url):
    for attempt in range(3):
        try:
            with urlopen(Request(url, headers={"User-Agent": "KKL-width-maximal-audit/1.0"}),
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
