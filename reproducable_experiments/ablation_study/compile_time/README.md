# Compile-time benchmark of the ablation-study proofs: **my method** vs **ablated**

Companion to `reproducable_experiments/compile_time/` (faithful vs. upstream monolith), but the two
worlds here are the two **ablation arms** — the proofs the two agents actually produced — measured
across **3 books of the 15** (Book 1, 2, 3).

- **mymethod** = the full method (skills + scripts + memory) — `out/mymethod/<label>/<run>/PropNN/`.
- **ablated**  = the bare-LLM arm (methodology stripped) — `out/ablated/<label>/<run>/PropNN/`.

Both were tasked to fill the *same* premapped proposition; only the produced proof differs. Here we
measure, **per produced proof**, the wall-clock to compile it cold in the real repo.

## Unit of measurement

Each `(arm, prop)` had up to **3 ablation-study runs**. Every run that **SUCCEEDED** produced a
zero-sorry, compiling `PropNN/` folder → we compile and time **each such proof independently** (so an
arm/prop with 1 success + 2 timeouts still contributes its 1 proof — the data is complete). A run
whose ablation-study result was **not** SUCCESS (TIMEOUT / FAIL) produced **no artifact** → recorded
as `nan`. The ablated arm solved only a handful of props, so most of its cells are `nan` by
construction (that is the finding, not a bug).

`out/<arm>/<label>_opus/<run_id>/result.txt` is the source of truth for which runs succeeded.

## Protocol (identical for both arms)

Per timing pass, per arm:

1. `rm -rf .lake/build` — wipe **all** our built content (SystemE + every Euclid lib). Does **not**
   touch `.lake/packages/` (Mathlib + external deps), so Mathlib is never rebuilt.
2. `lake build SystemE` — build the shared framework once (untimed).
3. Walk the props **in order**; for each successful run's proof:
   - `rm -rf Book<N>/Prop<NN>` then `cp -r <generated PropNN>/ Book<N>/Prop<NN>` — swap the repo's own
     proof folder for the generated one.
   - **Warm** (untimed): `lake build Book<N>.Prop<NN>.Main` — builds the proof AND every cited-prop /
     shared-library / Mathlib-tactic olean it depends on.
   - **Invalidate only this prop's own artifacts**: `rm -rf .lake/build/{lib,ir}/Book<N>/Prop<NN>` —
     deletes just this proposition's `step*`/`Main` oleans; every dependency stays warm.
   - **Time**: `timeout <CAP> lake build Book<N>.Prop<NN>.Main` — recompiles *only* the produced
     proof's own files (deps served from cache). This is the recorded `wall_s`.
   - `rm -rf Book<N>/Prop<NN>` then `git checkout HEAD -- Book<N>/Prop<NN>` — **revert** to the repo's
     tracked proof exactly, before moving on.

**Why warm-then-time.** `.lake/build` is wiped only once per arm/pass, so a *naive* single cold build
would charge the FIRST attempt of each prop the one-time cost of building its whole dependency cone
(cited props, Mathlib tactic modules) while attempts 2–3 reuse those cached oleans — inflating the
first bar for a reason that has nothing to do with the proof or the method. The cited deps are the
repo's OWN proofs, identical across arms and attempts, and are **not part of the produced proof** we
want to measure. So we warm the deps, drop only the target prop's oleans, and time the recompile of
just its own files — every attempt (1/2/3) and both arms start from an identical warm cache. SMT is
uncapped (SystemE default on this branch), so the per-build wall cap (`CAP`, default 3600s) is the
sole cutoff. Same uncapped SMT + same wall + same `-j` + same exclusive node for both arms.

The whole sweep is repeated `NUM_RUNS` times (default 3) for compile-noise stability.

## Run

```bash
sbatch reproducable_experiments/ablation_study/compile_time/submit.sbatch
```

or interactively:

```bash
srun --partition=compute --constraint=EPYC_9634 --exclusive --pty bash
bash reproducable_experiments/ablation_study/compile_time/run_timing.sh
```

Tunables (env): `CAP` = per-build wall seconds (default `3600`), `NUM_RUNS` = timing passes (default `3`).

> The driver mutates `Book<N>/Prop<NN>` folders in the working tree and reverts them with
> `git checkout HEAD -- …` after every build. Run it on a **clean** working tree (the target folders
> must be committed) so the revert restores the intended proof. It is a **human/SLURM-run** script.

## Output

`results/pass<id>_<datetime>/{mymethod.csv,ablated.csv,build.log,meta.txt}`. Each CSV:

```
label,run_id,wall_s,status
Book1_Prop06,20260722-011540-c975f507,73.42,ok
Book1_Prop20,20260719-193910-f8f2bbe9,nan,TIMEOUT
```

`ok` = compiled (`wall_s` = cold build time); `T.O.` = hit the wall cap; `fail` = build errored;
otherwise the ablation-study status (`TIMEOUT`, …) with `wall_s = nan` (no artifact to compile).

## Export for the paper

```bash
python3 reproducable_experiments/ablation_study/compile_time/export_paper_data.py
```

Reads `results/pass*/` → writes `paper/data/ablation_compile/{runs.csv, by_proof.dat, by_prop.dat,
summary_by_arm.dat}` (whitespace-delimited, single header, `nan` for never-compiled cells).
