#!/usr/bin/env python3
"""Aggregate per-experiment metrics straight from the .jsonl transcripts (NOT status.md,
whose /usage wall-time is inflated by idle/resume gaps).

Per transcript (one session = one prop x one method):
  turns         = number of assistant messages (API responses)
  wall_s        = last_timestamp - first_timestamp   (real elapsed span)
  wall_per_turn = wall_s / turns
  total_tokens  = sum over turns of input + output + cache_creation + cache_read
  tok_per_turn  = total_tokens / turns

Run bare:  python3 reproducable_experiments/fill_comparison_study/analyze_transcripts.py
Writes transcript_metrics.csv next to itself; prints a table + totals.
"""
import json
import csv
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
METHODS = {"naive": HERE / "naive_llm", "mine": HERE / "my_method"}


def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def analyze(jsonl: Path):
    turns = 0
    tokens = 0
    tmin = tmax = None
    for line in jsonl.open(errors="replace"):
        try:
            obj = json.loads(line)
        except Exception:
            continue
        ts = obj.get("timestamp")
        if ts:
            t = parse_ts(ts)
            tmin = t if tmin is None or t < tmin else tmin
            tmax = t if tmax is None or t > tmax else tmax
        if obj.get("type") == "assistant":
            turns += 1
            u = (obj.get("message") or {}).get("usage") or {}
            tokens += (u.get("input_tokens", 0) + u.get("output_tokens", 0)
                       + u.get("cache_creation_input_tokens", 0) + u.get("cache_read_input_tokens", 0))
    wall = (tmax - tmin).total_seconds() if tmin and tmax else 0
    return dict(turns=turns, wall_s=round(wall, 1), tokens=tokens)


def hms(sec):
    sec = int(round(sec))
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h}h{m:02d}m{s:02d}s" if h else f"{m}m{s:02d}s"


def humtok(n):
    return f"{n/1e6:.1f}M" if n >= 1e6 else f"{n/1e3:.1f}k"


rows = []
for method, root in METHODS.items():
    for jsonl in sorted(root.glob("*/*.jsonl")):
        prop = jsonl.parent.name
        a = analyze(jsonl)
        a.update(prop=prop, method=method,
                 wall_per_turn_s=round(a["wall_s"] / a["turns"], 1) if a["turns"] else None,
                 tok_per_turn=round(a["tokens"] / a["turns"]) if a["turns"] else None)
        rows.append(a)

order = {"naive": 0, "mine": 1}
rows.sort(key=lambda r: (tuple(int(x) for x in r["prop"].split(".")), order[r["method"]]))

print("| prop | method | turns | wall | wall/turn | total tokens | tokens/turn |")
print("|:----:|:------:|------:|-----:|----------:|-------------:|------------:|")
for r in rows:
    print(f"| {r['prop']} | {r['method']} | {r['turns']} | {hms(r['wall_s'])} | "
          f"{r['wall_per_turn_s']}s | {humtok(r['tokens'])} | {humtok(r['tok_per_turn'])} |")

print()
for method in ("naive", "mine"):
    sub = [r for r in rows if r["method"] == method]
    T = sum(r["turns"] for r in sub)
    W = sum(r["wall_s"] for r in sub)
    K = sum(r["tokens"] for r in sub)
    print(f"**{method} totals** — turns {T} | wall {hms(W)} | wall/turn {W/T:.1f}s | "
          f"tokens {humtok(K)} | tokens/turn {humtok(K/T)}")

out = HERE / "transcript_metrics.csv"
with open(out, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=["prop", "method", "turns", "wall_s",
                                       "wall_per_turn_s", "tokens", "tok_per_turn"])
    w.writeheader()
    for r in rows:
        w.writerow({k: r.get(k) for k in w.fieldnames})
print(f"\nwrote {out}")
