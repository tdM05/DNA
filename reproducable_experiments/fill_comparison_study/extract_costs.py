#!/usr/bin/env python3
"""Parse the two status.md files and tabulate per-prop cost/time/code-churn for
ordered decomposition (my_method) vs naive LLM (naive_llm).

Run bare:  python3 reproducable_experiments/fill_comparison_study/extract_costs.py
Writes costs_comparison.csv next to itself and prints a markdown table + totals.
"""
import re
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
FILES = {"naive": HERE / "naive_llm" / "status.md", "mine": HERE / "my_method" / "status.md"}


def dur_to_sec(s: str):
    tot = 0
    for val, unit in re.findall(r"(\d+)\s*([hms])", s.strip()):
        tot += int(val) * {"h": 3600, "m": 60, "s": 1}[unit]
    return tot


def sec_to_hms(sec):
    if sec is None:
        return ""
    h, r = divmod(int(sec), 3600)
    m, s = divmod(r, 60)
    return f"{h}h{m:02d}m{s:02d}s" if h else f"{m}m{s:02d}s"


def parse(path: Path):
    """status.md -> {prop: {cost, api_s, wall_s, added, removed}}"""
    props, cur = {}, None
    for line in path.read_text().splitlines():
        m = re.match(r"###\s+(\S+)", line)
        if m:
            cur = m.group(1)
            props[cur] = {}
            continue
        if cur is None:
            continue
        d = props[cur]
        if (mc := re.search(r"Total cost:\s*\$([\d.]+)", line)):
            d["cost"] = float(mc.group(1))
        elif (ma := re.search(r"Total duration \(API\):\s*(.+)", line)):
            d["api_s"] = dur_to_sec(ma.group(1))
        elif (mw := re.search(r"Total duration \(wall\):\s*(.+)", line)):
            d["wall_s"] = dur_to_sec(mw.group(1))
        elif (mh := re.search(r"Total code changes:\s*(\d+) lines added, (\d+) lines removed", line)):
            d["added"], d["removed"] = int(mh.group(1)), int(mh.group(2))
    return props


data = {k: parse(v) for k, v in FILES.items()}
props = sorted(set(data["naive"]) | set(data["mine"]),
               key=lambda p: tuple(int(x) for x in p.split(".")))

rows = []
for p in props:
    n, m = data["naive"].get(p, {}), data["mine"].get(p, {})
    rows.append(dict(
        prop=p,
        naive_cost=n.get("cost"), mine_cost=m.get("cost"),
        cost_ratio=(round(m["cost"] / n["cost"], 2) if n.get("cost") and m.get("cost") else None),
    ))


def money(x):
    return f"${x:,.2f}" if isinstance(x, (int, float)) else ""


print("| prop | naive $ | mine $ | mine/naive |")
print("|:----:|--------:|-------:|:----------:|")
for r in rows:
    ratio = f"{r['cost_ratio']}x" if r["cost_ratio"] else ""
    print(f"| {r['prop']} | {money(r['naive_cost'])} | {money(r['mine_cost'])} | {ratio} |")


def total(meth):
    return sum(data[meth][p].get("cost", 0) or 0 for p in data[meth])


tn, tm = total("naive"), total("mine")
print(f"\n**Totals** — naive {money(tn)}  vs  mine {money(tm)}  (mine = {tm / tn:.1f}× naive)")

out = HERE / "costs_comparison.csv"
with open(out, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
    w.writeheader()
    w.writerows(rows)
print(f"\nwrote {out}")
