#!/usr/bin/env python3
"""Export compile-time benchmark results to paper/data/compile/ for TikZ/pgfplots.

PURE READ of results/run*/<new|old>.csv  ->  WRITE paper/data/compile/*.
Never touches results/. Deterministic + idempotent. Commit the outputs to git so
the paper builds even if results/ is cleared.

World labels: new = faithful decomposed proofs, old = original monolith.
A `T.O.` row is CENSORED (did not finish within the cap) -> it is a LOWER BOUND on
time, not a true time; plotted AT the cap and flagged, never averaged as a real value.

Outputs
-------
runs.csv               canonical lossless, one row per (world, prop, run).
by_prop.dat            wide, one row per prop: old_* and new_* side by side
                       -> per-prop bars AND the old-vs-new scatter.
cactus.dat             one row per rank: each world's times sorted ascending
                       (censored props sorted to the tail at the cap)
                       -> the cactus / sorted-tail plot (per-world sort is a
                       real aggregation pgfplots cannot do itself).
summary_by_world.dat   one row per world: compiled count, median/max over ok runs.
"""
import os, glob, csv, statistics

BASE     = "/u/taddmao/code/autoform/DNA/reproducable_experiments/compile_time"
RES_DIR  = os.path.join(BASE, "results")
DATA_DIR = "/u/taddmao/code/autoform/DNA/paper/data/compile"
WORLDS   = ["new", "old"]


def read_world_csv(path):
    """results/run*/<world>.csv -> list of (prop:int, wall_s:float, status:str)."""
    out = []
    with open(path) as f:
        for row in csv.DictReader(f):
            out.append((int(row["target"]), float(row["wall_s"]), row["status"].strip()))
    return out


def collect():
    """One record per (world, prop, run), sorted (world, prop, run_id)."""
    rows = []
    for run_dir in sorted(glob.glob(os.path.join(RES_DIR, "run*"))):
        run_id = os.path.basename(run_dir)
        for world in WORLDS:
            csv_path = os.path.join(run_dir, f"{world}.csv")
            if not os.path.exists(csv_path):
                continue
            for prop, wall, status in read_world_csv(csv_path):
                rows.append(dict(
                    world=world, prop=prop, run_id=run_id,
                    wall_s=wall, status=status,
                    ok=int(status == "ok"),
                    timeout=int(status == "T.O."),
                ))
    rows.sort(key=lambda r: (r["world"], r["prop"], r["run_id"]))
    return rows


def cap_seconds(rows):
    """The wall cap = the largest censored (T.O.) wall recorded."""
    tos = [r["wall_s"] for r in rows if r["timeout"]]
    return max(tos) if tos else float("nan")


def group(rows, *keys):
    g = {}
    for r in rows:
        g.setdefault(tuple(r[k] for k in keys), []).append(r)
    return g


def write_runs_csv(rows):
    cols = ["world", "prop", "run_id", "wall_s", "status", "ok", "timeout"]
    path = os.path.join(DATA_DIR, "runs.csv")
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: (f"{r[c]:.2f}" if isinstance(r[c], float) else r[c]) for c in cols})
    return path


def per_prop_stats(rows, world, prop, cap):
    """mean/std over the OK runs of this (world,prop); plot value censored at cap."""
    rs = [r for r in rows if r["world"] == world and r["prop"] == prop]
    ok = [r["wall_s"] for r in rs if r["ok"]]
    n_to = sum(r["timeout"] for r in rs)
    censored = int(len(ok) == 0)                       # never compiled in any run
    mean = statistics.mean(ok) if ok else float("nan")
    std = statistics.pstdev(ok) if len(ok) >= 2 else 0.0
    plot = mean if ok else cap                         # censored -> pinned at cap
    return dict(n_runs=len(rs), n_ok=len(ok), n_to=n_to,
                mean=mean, std=std, plot=plot, censored=censored)


def write_by_prop(rows, cap):
    """Wide: one row per prop, old_* and new_* side by side (scatter + bars)."""
    props = sorted({r["prop"] for r in rows})
    path = os.path.join(DATA_DIR, "by_prop.dat")
    hdr = ["prop",
           "new_mean", "new_std", "new_n_ok", "new_n_to", "new_plot", "new_censored",
           "old_mean", "old_std", "old_n_ok", "old_n_to", "old_plot", "old_censored",
           "speedup"]
    lines = []
    for prop in props:
        n = per_prop_stats(rows, "new", prop, cap)
        o = per_prop_stats(rows, "old", prop, cap)
        # speedup = old/new using plot values (censored old counts at the cap ->
        # a LOWER bound on the true speedup); guard div-by-zero.
        speedup = (o["plot"] / n["plot"]) if n["plot"] else float("nan")
        lines.append([prop,
                      f'{n["mean"]:.2f}' if n["n_ok"] else "nan", f'{n["std"]:.2f}',
                      n["n_ok"], n["n_to"], f'{n["plot"]:.2f}', n["censored"],
                      f'{o["mean"]:.2f}' if o["n_ok"] else "nan", f'{o["std"]:.2f}',
                      o["n_ok"], o["n_to"], f'{o["plot"]:.2f}', o["censored"],
                      f"{speedup:.2f}"])
    with open(path, "w") as f:
        f.write(" ".join(hdr) + "\n")
        for ln in lines:
            f.write(" ".join(str(x) for x in ln) + "\n")
    return path


def write_cactus(rows, cap):
    """One row per rank: each world's per-prop plot-times sorted ascending.
    Censored props carry the cap value, so they land in the tail. pgfplots has no
    per-column independent sort, so we materialize it here."""
    props = sorted({r["prop"] for r in rows})
    series = {}
    for world in WORLDS:
        vals = [per_prop_stats(rows, world, p, cap)["plot"] for p in props]
        series[world] = sorted(vals)
    path = os.path.join(DATA_DIR, "cactus.dat")
    with open(path, "w") as f:
        f.write("rank new_sorted old_sorted\n")
        for i in range(len(props)):
            f.write(f"{i+1} {series['new'][i]:.2f} {series['old'][i]:.2f}\n")
    return path


def write_summary(rows, cap):
    path = os.path.join(DATA_DIR, "summary_by_world.dat")
    props = sorted({r["prop"] for r in rows})
    lines = []
    for world in WORLDS:
        stats = [per_prop_stats(rows, world, p, cap) for p in props]
        compiled = [s["mean"] for s in stats if s["n_ok"]]          # props that ever compiled
        n_props = len(props)
        n_compiled = len(compiled)
        n_censored = sum(s["censored"] for s in stats)              # props never finished
        med = statistics.median(compiled) if compiled else float("nan")
        mx = max(compiled) if compiled else float("nan")
        # total wall over all runs (censored counted at cap = lower bound)
        tot = sum(r["wall_s"] for r in rows if r["world"] == world)
        lines.append([world, n_props, n_compiled, n_censored,
                      f"{med:.2f}", f"{mx:.2f}", f"{tot:.1f}"])
    with open(path, "w") as f:
        f.write("world n_props n_compiled n_censored median_ok_s max_ok_s total_wall_s\n")
        for ln in lines:
            f.write(" ".join(str(x) for x in ln) + "\n")
    return path, lines


def main():
    os.makedirs(DATA_DIR, exist_ok=True)
    rows = collect()
    assert rows, "no run CSVs found under " + RES_DIR
    cap = cap_seconds(rows)
    n_runs = len({r["run_id"] for r in rows})
    p1 = write_runs_csv(rows)
    p2 = write_by_prop(rows, cap)
    p3 = write_cactus(rows, cap)
    p4, summ = write_summary(rows, cap)
    print(f"{len(rows)} rows across {n_runs} runs x {len(WORLDS)} worlds; cap = {cap:.0f}s")
    for p in (p1, p2, p3, p4):
        print("wrote:", p)
    print("\nper-world summary:")
    print("  world  props compiled censored median_ok  max_ok  total_wall")
    for w, n_props, n_comp, n_cens, med, mx, tot in summ:
        print(f"  {w:<5} {n_props:>6} {n_comp:>8} {n_cens:>8} {med:>9} {mx:>8} {tot:>10}")


if __name__ == "__main__":
    main()
