#!/usr/bin/env python3
"""Export ablation-study results to paper/data/ for TikZ/pgfplots.

PURE READ of out/<mode>/<label>/<run_id>/result.txt  ->  WRITE paper/data/*.
Never touches out/. Deterministic + idempotent: re-running reproduces byte-identical
files (given the same out/). Commit the outputs to git so the paper builds even if
out/ is cleared.

Outputs
-------
runs.csv            canonical, lossless, one row per run (comma-sep, has strings).
summary_by_arm.dat  one row per arm  -> cost-vs-coverage scatter (pgfplots).
by_prop.dat         one row per (arm,prop) -> per-prop outcome strip (pgfplots).

All .dat files are whitespace-delimited with a single header row and NO NaN,
so `\\pgfplotstableread{file.dat}\\tbl` reads them directly.
"""
import os, glob, re, csv, statistics

OUT_BASE = "/home/user/code/autoform/DNA/reproducable_experiments/ablation_study/out"
DATA_DIR = "/home/user/code/autoform/DNA/paper/data/ablation"
MODEL    = "opus"
TARGET_RUNS   = 3
WALL_LIMIT_HR = 12.0          # global watchdog: a TIMEOUT run's true wall is the cap
TERMINAL = {"SUCCESS", "GAVEUP", "FAIL", "TIMEOUT"}


def parse_result(path):
    d = {}
    with open(path) as f:
        for line in f:
            k, sep, v = line.partition(":")
            if sep:
                d[k.strip()] = v.strip()
    return d


def collect():
    """One record per run, sorted deterministically (mode, book, prop, run_id)."""
    rows = []
    for run_dir in glob.glob(os.path.join(OUT_BASE, "*", f"*_{MODEL}", "*")):
        rpath = os.path.join(run_dir, "result.txt")
        if not os.path.isdir(run_dir) or not os.path.exists(rpath):
            continue
        parts = run_dir.rstrip(os.sep).split(os.sep)
        mode, label, run_id = parts[-3], parts[-2], parts[-1]
        d = parse_result(rpath)
        result = d.get("result", "RUNNING").upper()

        mb = re.search(r"Book0*(\d+)", label)
        mp = re.search(r"Prop0*(\d+)", label)
        book = int(mb.group(1)) if mb else -1
        prop = int(mp.group(1)) if mp else -1

        wall = float(d["wall_sec"]) if d.get("wall_sec") not in (None, "") else float("nan")
        # TIMEOUT: result.txt wall_sec is a stale per-round value; the watchdog killed
        # the run at exactly the 12h cap, so the cap IS the true wall.
        if result == "TIMEOUT":
            wall = WALL_LIMIT_HR * 3600.0
        cost = float(d["cost_usd"]) if d.get("cost_usd") not in (None, "") else float("nan")

        rows.append(dict(
            mode=mode, book=book, prop=prop,
            prop_label=f"{book}.{prop:02d}", run_id=run_id,
            result=result,
            success=int(result == "SUCCESS"),
            timeout=int(result == "TIMEOUT"),
            finished=int(result in TERMINAL),
            wall_sec=wall, wall_hr=wall / 3600.0, cost_usd=cost,
        ))
    rows.sort(key=lambda r: (r["mode"], r["book"], r["prop"], r["run_id"]))
    # stable per-prop attempt index
    seen = {}
    for r in rows:
        key = (r["mode"], r["book"], r["prop"])
        seen[key] = seen.get(key, 0) + 1
        r["attempt"] = seen[key]
    return rows


def write_runs_csv(rows):
    cols = ["mode", "book", "prop", "prop_label", "attempt", "run_id",
            "result", "success", "timeout", "finished",
            "wall_sec", "wall_hr", "cost_usd"]
    path = os.path.join(DATA_DIR, "runs.csv")
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: (f"{r[c]:.4f}" if isinstance(r[c], float) else r[c]) for c in cols})
    return path


def group(rows, *keys):
    g = {}
    for r in rows:
        g.setdefault(tuple(r[k] for k in keys), []).append(r)
    return g


def write_by_prop(rows):
    """One row per (arm, prop): outcome counts + a regime code for the strip.
    regime: 2 = solved-all (k/k), 1 = flaky (partial), 0 = ceiling (0/k)."""
    path = os.path.join(DATA_DIR, "by_prop.dat")
    recs = []
    for (mode, book, prop), rs in group(rows, "mode", "book", "prop").items():
        n = len(rs)
        n_ok = sum(r["success"] for r in rs)
        n_to = sum(r["timeout"] for r in rs)
        regime = 2 if n_ok == n else (0 if n_ok == 0 else 1)
        recs.append((mode, f"{book}.{prop:02d}", book, prop, n, n_ok, n_to, regime))
    recs.sort(key=lambda t: (t[0], t[2], t[3]))
    with open(path, "w") as f:
        f.write("arm prop_label book prop n_runs n_success n_timeout regime\n")
        for t in recs:
            f.write("{} {} {} {} {} {} {} {}\n".format(*t))
    return path


def write_by_prop_wide(rows):
    """Wide: one row per prop, both arms side by side, with a sequential x index.
    n_success out of k for each arm -> grouped per-prop bars in pgfplots."""
    path = os.path.join(DATA_DIR, "by_prop_wide.dat")
    props = sorted({(r["book"], r["prop"]) for r in rows})
    g = group(rows, "mode", "book", "prop")
    lines = []
    for i, (book, prop) in enumerate(props):
        abl = g.get(("ablated", book, prop), [])
        mine = g.get(("mymethod", book, prop), [])
        a_ok = sum(r["success"] for r in abl)
        m_ok = sum(r["success"] for r in mine)
        lines.append((i, f"{book}.{prop:02d}", a_ok, len(abl), m_ok, len(mine)))
    with open(path, "w") as f:
        f.write("idx prop_label abl_success abl_runs mine_success mine_runs\n")
        for t in lines:
            f.write("{} {} {} {} {} {}\n".format(*t))
    return path


def write_wall_by_prop(rows):
    """Per-prop wall time (hours) for the horizontal bar figure -- ALL 3 runs, no
    averaging. One column per run per arm (base_r1..3, mine_r1..3), in book/prop
    order. A timed-out run sits honestly at its 12h cap (pinned in collect()),
    so no censoring/averaging games are needed. Missing runs -> nan (skipped)."""
    path = os.path.join(DATA_DIR, "wall_by_prop.dat")
    props = sorted({(r["book"], r["prop"]) for r in rows})
    g = group(rows, "mode", "book", "prop")
    K = TARGET_RUNS

    def arm_runs(arm, book, prop):
        rs = sorted(g.get((arm, book, prop), []), key=lambda r: r["run_id"])
        walls = [f'{r["wall_hr"]:.3f}' for r in rs][:K]
        walls += ["nan"] * (K - len(walls))          # pad to K
        return walls

    recs = []
    for book, prop in props:
        recs.append((book, prop, f"{book}.{prop:02d}",
                     arm_runs("ablated", book, prop),
                     arm_runs("mymethod", book, prop)))
    recs.sort(key=lambda t: (t[0], t[1]))

    bcols = " ".join(f"base_r{i+1}" for i in range(K))
    mcols = " ".join(f"mine_r{i+1}" for i in range(K))
    with open(path, "w") as f:
        f.write(f"ypos prop_label {bcols} {mcols}\n")
        for y, (_, _, label, b, m) in enumerate(recs):
            f.write(f"{y} {label} " + " ".join(b) + " " + " ".join(m) + "\n")
    return path


def write_summary_by_arm(rows):
    """One row per arm for the cost-vs-coverage scatter + CE. All numeric."""
    path = os.path.join(DATA_DIR, "summary_by_arm.dat")
    lines = []
    for (mode,), rs in sorted(group(rows, "mode").items()):
        props = group(rs, "book", "prop")
        n_props = len(props)
        # coverage / reliability
        pass1 = sum(r["success"] for r in rs) / len(rs)               # per-run rate
        pass_k = sum(1 for p in props.values() if any(x["success"] for x in p)) / n_props
        allk = sum(1 for p in props.values()
                   if all(x["success"] for x in p) and len(p) == TARGET_RUNS) / n_props
        # cost among SOLVED runs only (apples-to-apples)
        solved = [r for r in rs if r["success"]]
        med_wall = statistics.median(r["wall_hr"] for r in solved) if solved else float("nan")
        med_cost = statistics.median(r["cost_usd"] for r in solved) if solved else float("nan")
        # spend over ALL attempts (charges failures) + proofs delivered (pass@k)
        tot_cost = sum(r["cost_usd"] for r in rs)
        tot_wall = sum(r["wall_hr"] for r in rs)
        n_delivered = sum(1 for p in props.values() if any(x["success"] for x in p))
        slots_burned = sum(1 for r in rs if r["timeout"])
        ce_dollar = n_delivered / tot_cost              # proofs per $
        ce_wall   = n_delivered / tot_wall              # proofs per wall-hour
        lines.append((mode, n_props, round(pass1, 4), round(pass_k, 4), round(allk, 4),
                      round(med_wall, 4), round(med_cost, 4),
                      round(tot_cost, 2), round(tot_wall, 2),
                      n_delivered, slots_burned,
                      round(ce_dollar, 5), round(ce_wall, 5)))
    with open(path, "w") as f:
        f.write("arm n_props pass1 passk allk med_wall_solved_h med_cost_solved "
                "tot_cost tot_wall_h n_delivered slots_burned ce_dollar ce_wall\n")
        for t in lines:
            f.write(" ".join(str(x) for x in t) + "\n")
    return path, lines


def main():
    os.makedirs(DATA_DIR, exist_ok=True)
    rows = collect()
    assert rows, "no runs found under " + OUT_BASE
    running = [r for r in rows if not r["finished"]]
    p1 = write_runs_csv(rows)
    p2 = write_by_prop(rows)
    p2w = write_by_prop_wide(rows)
    p2wall = write_wall_by_prop(rows)
    p3, summ = write_summary_by_arm(rows)
    print(f"{len(rows)} runs exported ({len(running)} non-terminal -- expected 0)")
    for p in (p1, p2, p2w, p2wall, p3):
        print("wrote:", p)
    print("\nper-arm summary:")
    hdr = ["arm", "props", "pass@1", "pass@k", "all@k", "medWall", "medCost",
           "totCost", "totWall", "deliv", "burned", "CE$", "CEwall"]
    print("  " + " ".join(f"{h:>8}" for h in hdr))
    for t in summ:
        print("  " + " ".join(f"{str(x):>8}" for x in t))


if __name__ == "__main__":
    main()
