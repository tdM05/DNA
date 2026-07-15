# Compile-time benchmark: faithful `Book1` vs original `OldBook1`

Measures, **per proposition**, the wall-clock time to compile that proposition *from cold* in two worlds:

- **new** = the faithful, decomposed proofs — `Book1/PropN/Main.lean` (+ its `stepK.lean` files).
- **old** = the original monolithic upstream proofs — `OldBook1/PropN.lean` (pristine LeanEuclid, `f35d0da`).

Both prove the *same* `proposition_N`; only the proof structure differs.

## Layout

```
compile_time/
  run_timing.sh      # the driver
  submit.sbatch      # SLURM wrapper (1 exclusive EPYC_9634 node)
  results/           # TRACKED: <new|old>_<host>_<stamp>.csv + run_meta_<jobid>.txt
  slurm_output/      # untracked: SLURM stdout logs
  slurm_err/         # untracked: SLURM stderr logs
```

## Protocol

Per world, symmetric and clean:

1. `rm -rf .lake/build` — wipe **all** our built content (SystemE + every Euclid lib). Does **not** touch
   `.lake/packages/` (Mathlib + external deps), so Mathlib is never rebuilt.
2. `lake build SystemE` — build the shared framework once (untimed); reuses cached Mathlib.
3. Time each target cold, ascending, one at a time: `timeout 600 lake build -j1 <target>`.

Then repeat 1–3 for the other world → both start from an identical clean state.

- **new pass:** times `Book1.Prop01.Main` … `Book1.Prop48.Main`. `Helpers` (faithful-only) is not built
  separately — the first prop that imports it (Prop38, ascending) builds the whole lib, so that cost is
  counted there, exactly as it should be. The monolith re-derives those facts inline instead.
- **old pass:** times `OldBook1.Prop01` … `OldBook1.Prop48` (never builds `Helpers` — upstream doesn't use it).

SMT is uncapped (`systemE.solverTime` default raised to 100000 in `SystemE/Meta/Smt/Solver.lean` on this
branch), so the **10-min wall is the sole cutoff**. Same uncapped SMT + same wall + same `-j1` + same exclusive
`EPYC_9634` node for both worlds.

## Run

```bash
cd /h/56/taddmao/code/autoform/DNA
sbatch reproducable_experiments/compile_time/submit.sbatch
```

or interactively:

```bash
srun --partition=cpunodes --constraint=EPYC_9634 --exclusive --pty bash
bash reproducable_experiments/compile_time/run_timing.sh
```

Tunables (env): `CAP` = per-prop wall seconds (default `600`), `JOBS` = `lake -j` (default `1`).

## Output

`results/new_<host>_<stamp>.csv` and `results/old_<host>_<stamp>.csv` (48 rows each):

```
target,wall_s,status
01,4.31,ok
16,73.42,ok
22,600,T.O.
```

`ok` = compiled (`wall_s` = cold build time); `T.O.` = hit the wall cap; `fail` = errored (incl. a build whose
earlier-failed dependency is missing — same rule in both worlds). `results/run_meta_<jobid>.txt` records host,
CPU, git commit, cap/jobs, solver paths.
