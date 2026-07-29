#!/usr/bin/env python3
"""Export the ablation compile-time benchmark to paper/data/ablation_compile/ for TikZ/pgfplots.

PURE READ of results/pass*/<mymethod|ablated>.csv  ->  WRITE paper/data/ablation_compile/*.
Never touches results/. Deterministic + idempotent. Commit the outputs to git so the paper builds
even if results/ is cleared.

Arms: mymethod = full method (skills + scripts + memory) proofs; ablated = bare-LLM proofs.
Each (arm, prop) had up to 3 ablation-study RUNS; only the SUCCESS runs produced a compiling proof.
A run whose ablation-study result was not SUCCESS (TIMEOUT / FAIL) produced NO artifact -> its
compile time is `nan` (never compiled), carried through so the data is complete. The ablated arm
solved only a handful of props, so most of its cells are nan by construction.

Within a compiled proof, the timing sweep is repeated NUM_RUNS passes; we average the OK passes.

Outputs
-------
runs.csv               canonical lossless: one row per (arm, prop, ablation_run, timing_pass).
by_proof.dat           one row per (arm, prop, ablation_run): mean/std compile time over timing passes.
by_prop.dat            wide, one row per prop: mymethod vs ablated aggregated over its runs.
summary_by_arm.dat     one row per arm: #proofs compiled, median/max/total compile time.
"""
import os, glob, csv, re, statistics

BASE     = "/u/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/compile_time"
RES_DIR  = os.path.join(BASE, "results")
DATA_DIR = "/u/taddmao/code/autoform/DNA/paper/data/ablation/compile"
ARMS     = ["mymethod", "ablated"]
K_RUNS   = 3          # ablation attempts per (arm, prop) -> one bar each in the fig


def _f(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return float("nan")


def read_arm_csv(path):
    """results/pass*/<arm>.csv -> list of (label, run_id, wall_s:float|nan, status)."""
    out = []
    with open(path) as f:
        for row in csv.DictReader(f):
            out.append((row["label"], row["run_id"], _f(row["wall_s"]), row["status"].strip()))
    return out


def parse_label(label):
    b = re.search(r"Book0*(\d+)", label)
    p = re.search(r"Prop0*(\d+)", label)
    book = int(b.group(1)) if b else -1
    prop = int(p.group(1)) if p else -1
    return book, prop


def collect():
    """One record per (arm, prop, ablation_run, timing_pass), sorted deterministically."""
    rows = []
    for pass_dir in sorted(glob.glob(os.path.join(RES_DIR, "pass*"))):
        pass_id = os.path.basename(pass_dir)
        for arm in ARMS:
            csv_path = os.path.join(pass_dir, f"{arm}.csv")
            if not os.path.exists(csv_path):
                continue
            for label, run_id, wall, status in read_arm_csv(csv_path):
                book, prop = parse_label(label)
                rows.append(dict(
                    arm=arm, book=book, prop=prop, prop_label=f"{book}.{prop:02d}",
                    label=label, ablation_run=run_id, timing_pass=pass_id,
                    wall_s=wall, status=status,
                    ok=int(status == "ok"),
                    timeout=int(status == "T.O."),
                    compiled=int(status == "ok"),
                ))
    rows.sort(key=lambda r: (r["arm"], r["book"], r["prop"], r["ablation_run"], r["timing_pass"]))
    return rows


def group(rows, *keys):
    g = {}
    for r in rows:
        g.setdefault(tuple(r[k] for k in keys), []).append(r)
    return g


def write_runs_csv(rows):
    cols = ["arm", "book", "prop", "prop_label", "label", "ablation_run", "timing_pass",
            "wall_s", "status", "ok", "timeout", "compiled"]
    path = os.path.join(DATA_DIR, "runs.csv")
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: (f"{r[c]:.2f}" if isinstance(r[c], float) else r[c]) for c in cols})
    return path


def proof_stats(rs):
    """Aggregate the timing passes of ONE (arm, prop, ablation_run) proof."""
    ok = [r["wall_s"] for r in rs if r["ok"]]
    mean = statistics.mean(ok) if ok else float("nan")
    std = statistics.pstdev(ok) if len(ok) >= 2 else 0.0
    return dict(n_pass=len(rs), n_ok=len(ok), mean=mean, std=std)


def write_by_proof(rows):
    """One row per (arm, prop, ablation_run): mean/std compile time over timing passes.
    A never-compiled proof (no OK pass — e.g. an ablated TIMEOUT run) has mean = nan."""
    path = os.path.join(DATA_DIR, "by_proof.dat")
    recs = []
    for (arm, book, prop, run), rs in group(rows, "arm", "book", "prop", "ablation_run").items():
        s = proof_stats(rs)
        recs.append((arm, f"{book}.{prop:02d}", book, prop, run,
                     s["n_pass"], s["n_ok"],
                     f'{s["mean"]:.2f}' if s["n_ok"] else "nan", f'{s["std"]:.2f}'))
    recs.sort(key=lambda t: (t[0], t[2], t[3], t[4]))
    with open(path, "w") as f:
        f.write("arm prop_label book prop ablation_run n_pass n_ok mean_s std_s\n")
        for t in recs:
            f.write(" ".join(str(x) for x in t) + "\n")
    return path


def per_prop_arm(rows, arm, book, prop):
    """Aggregate all compiled proofs of an (arm, prop) over runs AND passes.
    mean over every OK (run, pass) measurement; n_proofs = distinct runs that ever compiled."""
    rs = [r for r in rows if r["arm"] == arm and r["book"] == book and r["prop"] == prop]
    ok = [r["wall_s"] for r in rs if r["ok"]]
    runs_ok = {r["ablation_run"] for r in rs if r["ok"]}
    return dict(n_meas=len(ok), n_proofs=len(runs_ok),
                mean=statistics.mean(ok) if ok else float("nan"),
                std=statistics.pstdev(ok) if len(ok) >= 2 else 0.0)


def write_by_prop(rows):
    """Wide: one row per prop, mymethod vs ablated side by side (bars + scatter).
    A prop the ablated arm never compiled -> abl_mean = nan (skipped by pgfplots)."""
    props = sorted({(r["book"], r["prop"]) for r in rows})
    path = os.path.join(DATA_DIR, "by_prop.dat")
    hdr = ["idx", "prop_label", "book", "prop",
           "mine_mean", "mine_std", "mine_nproofs",
           "abl_mean", "abl_std", "abl_nproofs", "speedup"]
    lines = []
    for i, (book, prop) in enumerate(props):
        m = per_prop_arm(rows, "mymethod", book, prop)
        a = per_prop_arm(rows, "ablated", book, prop)
        speedup = (a["mean"] / m["mean"]) if (m["n_meas"] and a["n_meas"] and m["mean"]) else float("nan")
        lines.append([i, f"{book}.{prop:02d}", book, prop,
                      f'{m["mean"]:.2f}' if m["n_meas"] else "nan", f'{m["std"]:.2f}', m["n_proofs"],
                      f'{a["mean"]:.2f}' if a["n_meas"] else "nan", f'{a["std"]:.2f}', a["n_proofs"],
                      f"{speedup:.2f}" if speedup == speedup else "nan"])
    with open(path, "w") as f:
        f.write(" ".join(hdr) + "\n")
        for ln in lines:
            f.write(" ".join(str(x) for x in ln) + "\n")
    return path


def write_compile_by_prop(rows):
    """Fig format (mirrors ../ablation/wall_by_prop.dat): one row per prop, both arms as
    separate per-attempt bars. base_r1..K = ablated attempts, mine_r1..K = mymethod attempts;
    each value = that attempt's MEAN compile time over the timing passes (seconds), nan if the
    attempt never compiled (ablated TIMEOUT/FAIL). Attempts sorted by ablation run_id so the
    column order is stable. Missing attempts -> nan (skipped by pgfplots)."""
    props = sorted({(r["book"], r["prop"]) for r in rows})
    g = group(rows, "arm", "book", "prop", "ablation_run")

    def arm_attempts(arm, book, prop):
        runs = sorted({r["ablation_run"] for r in rows
                       if r["arm"] == arm and r["book"] == book and r["prop"] == prop})
        vals = []
        for run in runs:
            s = proof_stats(g[(arm, book, prop, run)])
            vals.append(f'{s["mean"]:.3f}' if s["n_ok"] else "nan")
        vals = vals[:K_RUNS] + ["nan"] * (K_RUNS - len(vals))    # pad to K
        return vals

    path = os.path.join(DATA_DIR, "compile_by_prop.dat")
    bcols = " ".join(f"base_r{i+1}" for i in range(K_RUNS))
    mcols = " ".join(f"mine_r{i+1}" for i in range(K_RUNS))
    with open(path, "w") as f:
        f.write(f"ypos prop_label {bcols} {mcols}\n")
        for y, (book, prop) in enumerate(props):
            b = arm_attempts("ablated", book, prop)
            m = arm_attempts("mymethod", book, prop)
            f.write(f"{y} {book}.{prop:02d} " + " ".join(b) + " " + " ".join(m) + "\n")
    return path


def write_summary(rows):
    path = os.path.join(DATA_DIR, "summary_by_arm.dat")
    props = sorted({(r["book"], r["prop"]) for r in rows})
    lines = []
    for arm in ARMS:
        means = []
        n_props_compiled = 0
        for book, prop in props:
            s = per_prop_arm(rows, arm, book, prop)
            if s["n_meas"]:
                means.append(s["mean"])
                n_props_compiled += 1
        med = statistics.median(means) if means else float("nan")
        mx = max(means) if means else float("nan")
        tot = sum(r["wall_s"] for r in rows if r["arm"] == arm and r["ok"])
        lines.append([arm, len(props), n_props_compiled,
                      f"{med:.2f}", f"{mx:.2f}", f"{tot:.1f}"])
    with open(path, "w") as f:
        f.write("arm n_props n_props_compiled median_mean_s max_mean_s total_ok_wall_s\n")
        for ln in lines:
            f.write(" ".join(str(x) for x in ln) + "\n")
    return path, lines


def main():
    os.makedirs(DATA_DIR, exist_ok=True)
    rows = collect()
    assert rows, "no pass CSVs found under " + RES_DIR
    n_pass = len({r["timing_pass"] for r in rows})
    p1 = write_runs_csv(rows)
    p2 = write_by_proof(rows)
    p3 = write_by_prop(rows)
    p5 = write_compile_by_prop(rows)
    p4, summ = write_summary(rows)
    print(f"{len(rows)} measurements across {n_pass} timing pass(es) x {len(ARMS)} arms")
    for p in (p1, p2, p3, p5, p4):
        print("wrote:", p)
    print("\nper-arm summary:")
    print("  arm       props compiled  median   max     total_wall")
    for arm, n_props, n_comp, med, mx, tot in summ:
        print(f"  {arm:<9} {n_props:>5} {n_comp:>8} {med:>8} {mx:>8} {tot:>11}")


if __name__ == "__main__":
    main()
