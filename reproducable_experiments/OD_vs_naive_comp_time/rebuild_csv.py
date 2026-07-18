#!/usr/bin/env python3
"""Rebuild the `status` column of each results/run*/<world>.csv from that run's build.log,
keeping wall_s from the CSV (the log has no timings; durations only ever went to the CSV).

Why: a build that printed "Build completed successfully" is `ok` even if `lake` exited nonzero
because a freshly-built DEPENDENCY used `sorry` (that's allowed here -- only the tested Main node
must be sorry-free). The original run_timing.sh classified purely by exit code, so such builds were
mislabeled `fail`. This re-derives status from the log evidence. Times are untouched.

Backs up each original CSV to <world>.csv.orig once, then overwrites <world>.csv in place.
Run bare:  python3 reproducable_experiments/OD_vs_naive_comp_time/rebuild_csv.py
"""
import re
import shutil
from pathlib import Path

RESULTS = Path(__file__).resolve().parent / "results"
WORLDS = ("naive", "mine")


def own_dir(target: str) -> str:
    parts = target.split(".")             # 'Book1.Prop43.Main' -> 'Book1/Prop43/'
    return f"{parts[0]}/{parts[1]}/" if len(parts) >= 2 else target


def status_from_block(block: str, csv_status: str, target: str) -> str:
    if "Build completed successfully" in block:
        # Built. Rule: for PropN, a `sorry` is allowed ONLY in a cited PropK (K != N). So any
        # "declaration uses 'sorry'" whose file is under PropN's OWN dir (Main or a stepK) is INVALID.
        own = own_dir(target)
        for line in block.splitlines():
            if "declaration uses 'sorry'" in line and own in line:
                return "sorry_self"       # INVALID: PropN's own cone uses sorry (not a real, complete proof)
        return "ok"                       # any sorry is in a cited PropK (K != N) -> allowed
    if csv_status == "T.O.":
        return "T.O."                     # genuine wall-cap kill: log truncated, no completion line
    if "error:" in block:
        return "fail"                     # a real Lean error
    return csv_status                     # no evidence either way -> keep what the CSV had


def parse_log(logf: Path) -> dict:
    """build.log -> {world: {target: block_text}}. SystemE output (before any target marker) is ignored."""
    worlds = {}
    cur_world = None
    cur_tgt = None
    buf = []

    def flush():
        if cur_world and cur_tgt:
            worlds.setdefault(cur_world, {})[cur_tgt] = "\n".join(buf)

    for line in logf.read_text(errors="replace").splitlines():
        mw = re.match(r"\s*-- world=(\S+)", line)
        mt = re.match(r"=====\s+(\S+)\s+=====", line)
        if mw:
            flush(); cur_tgt = None; buf = []
            cur_world = mw.group(1)
        elif mt:
            flush(); buf = []
            cur_tgt = mt.group(1)
        else:
            buf.append(line)
    flush()
    return worlds


def main():
    rundirs = sorted(p for p in RESULTS.glob("run*") if p.is_dir())
    if not rundirs:
        print(f"no run* dirs under {RESULTS}")
        return
    for rd in rundirs:
        logf = rd / "build.log"
        if not logf.exists():
            print(f"{rd.name}: no build.log, skip")
            continue
        worlds = parse_log(logf)
        for world in WORLDS:
            csvf = rd / f"{world}.csv"
            if not csvf.exists():
                continue
            orig = rd / f"{world}.csv.orig"
            if not orig.exists():
                shutil.copy2(csvf, orig)              # one-time backup of the raw run
            lines = [l for l in orig.read_text().splitlines() if l.strip()]
            out, changed = [lines[0]], []
            for row in lines[1:]:
                tgt, wall, st = row.split(",")
                block = worlds.get(world, {}).get(tgt, "")
                newst = status_from_block(block, st, tgt) if block else st
                if newst != st:
                    changed.append(f"{tgt} {st}->{newst}")
                out.append(f"{tgt},{wall},{newst}")
            csvf.write_text("\n".join(out) + "\n")
            note = ("  [" + ", ".join(changed) + "]") if changed else ""
            print(f"{rd.name}/{world}.csv: {len(changed)} corrected{note}")


if __name__ == "__main__":
    main()
