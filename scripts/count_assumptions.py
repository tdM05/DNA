#!/usr/bin/env python3
"""Count @assumption tags across LeanEuclidPlus.

Reports, from the inline `.lean` comment tags (the source of truth) and the
`scripts/assumption_tags.json` sidecar:
  - total `-- @assumption (...)` declarations
  - `-- @assumption_valid`  (node-invisible, Phase B skips)
  - `-- @assumption_gap`    (a real node Phase B proves)

Run bare from the repo root:  python3 scripts/count_assumptions.py
Add --by-prop for a per-proposition breakdown.
"""
import json
import re
import sys
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent          # .../Pistis
LEP = REPO / "LeanEuclidPlus"
TAGS_JSON = LEP / "scripts" / "assumption_tags.json"

DECL_RE = re.compile(r"--\s*@assumption\s*\(")
VALID_RE = re.compile(r"--\s*@assumption_valid\b")
GAP_RE = re.compile(r"--\s*@assumption_gap\b")


def prop_key(path: Path) -> str:
    """e.g. .../LeanEuclidPlus/Book2/Prop04/Main.lean -> Book2/Prop04"""
    rel = path.relative_to(LEP)
    return "/".join(rel.parts[:2])


BOOKS = ("Book1", "Book2", "Book3")


def scan_lean():
    per = {}  # prop -> Counter(decl, valid, gap)
    files = [f for b in BOOKS for f in (LEP / b).rglob("*.lean")]
    for f in sorted(files):
        text = f.read_text(errors="replace")
        c = Counter()
        c["decl"] = len(DECL_RE.findall(text))
        c["valid"] = len(VALID_RE.findall(text))
        c["gap"] = len(GAP_RE.findall(text))
        if any(c.values()):
            k = prop_key(f)
            acc = per.setdefault(k, Counter())
            acc.update(c)
    return per


def scan_json():
    if not TAGS_JSON.exists():
        return None
    data = json.loads(TAGS_JSON.read_text())
    per = {}
    for prop, entries in data.items():
        if not prop.startswith(BOOKS):
            continue
        c = Counter()
        for _, meta in entries.items():
            tag = meta.get("tag")
            c["decl"] += 1
            if tag == "valid":
                c["valid"] += 1
            elif tag == "gap":
                c["gap"] += 1
        per[prop] = c
    return per


def totals(per):
    t = Counter()
    for c in per.values():
        t.update(c)
    return t


def main():
    by_prop = "--by-prop" in sys.argv

    lean = scan_lean()
    jsn = scan_json()

    lt = totals(lean)
    print("== Inline .lean comment tags (source of truth) ==")
    print(f"  @assumption declarations : {lt['decl']}")
    print(f"  @assumption_valid        : {lt['valid']}")
    print(f"  @assumption_gap          : {lt['gap']}")
    print(f"  props with any tag       : {len(lean)}")

    if jsn is not None:
        jt = totals(jsn)
        print("\n== scripts/assumption_tags.json sidecar ==")
        print(f"  entries (total)          : {jt['decl']}")
        print(f"  valid                    : {jt['valid']}")
        print(f"  gap                      : {jt['gap']}")
        print(f"  props recorded           : {len(jsn)}")
    else:
        print("\n(scripts/assumption_tags.json not found)")

    if by_prop:
        print("\n== Per-prop (inline lean: decl / valid / gap) ==")
        for k in sorted(lean):
            c = lean[k]
            print(f"  {k:20s}  {c['decl']:3d} / {c['valid']:3d} / {c['gap']:3d}")


if __name__ == "__main__":
    main()
