# Compile-time benchmark: faithful `Book1` vs original `OldBook1`

Measures, **per proposition**, the wall-clock time to compile that proposition *from cold* in two worlds:

- **new** = the faithful, decomposed proofs — `Book1/PropN/Main.lean` (+ its `stepK.lean` files).
- **old** = the original monolithic upstream proofs — `OldBook1/PropN.lean` (pristine LeanEuclid, commit `f35d0da`).

Both prove the *same* `proposition_N`; only the proof structure differs. The claim under test: the faithful
decomposition compiles faster / more robustly than the monolith.

## Protocol

For each world, dead simple and symmetric:

1. `rm -rf .lake/build` — wipe **all** of our built content (SystemE + every Euclid lib). This does **not**
   touch `.lake/packages/` (Mathlib + aesop/batteries/smt/… live there), so Mathlib is never rebuilt.
2. `lake build SystemE` — build the shared logical framework once (untimed). Reuses the cached Mathlib.
3. Time each target cold, ascending, **one at a time**: `timeout 600 lake build -j1 <target>`.

Then repeat 1–3 for the other world. Both worlds thus start from an **identical clean state**.

- **new pass:** times `Helpers` first (its own row — it's a faithful-only shared library, so its cost is
  counted and visible, never hidden inside a prop), then `Book1.Prop01.Main` … `Book1.Prop48.Main`.
- **old pass:** times `OldBook1.Prop01` … `OldBook1.Prop48`. (Never builds `Helpers` — the upstream proofs
  don't use it.)

### Why it's fair (no reviewer questions)

- Identical clean build for both worlds; nothing Euclid is prebuilt, so no cached `.olean` can hide work.
- **Same** uncapped SMT + **same** 10-min wall cap + **same** `-j1` serial builds + **same** exclusive
  `EPYC_9634` node.
- SMT is uncapped so that the *wall cap is the single cutoff* — see below.

### SMT uncap

`euclid_finish` normally caps each solver (z3, then cvc5) at `systemE.solverTime` = 300 s. That would make a
hard prop fail with "could not prove" at ~600 s, colliding with the wall cap. So on this branch the lakefile
package `leanOptions` sets `systemE.solverTime = 100000` (~27 h), i.e. effectively uncapped, and the external
`timeout 600` is the sole limit. Revert with `git checkout LeanEuclidPlus/lakefile.lean`.

## Run

```bash
cd /h/56/taddmao/code/autoform/DNA
sbatch reproducable_experiments/submit.sbatch
```

or interactively:

```bash
srun --partition=cpunodes --constraint=EPYC_9634 --exclusive --pty bash
bash reproducable_experiments/run_timing.sh
```

Tunables (env): `CAP` = per-prop wall seconds (default `600`), `JOBS` = `lake -j` (default `1`).

## Output

`results/new_<host>_<stamp>.csv` (49 rows: `Helpers` + 48 props) and `results/old_<host>_<stamp>.csv` (48 rows):

```
target,wall_s,status
01,4.31,ok
16,73.42,ok
22,600,T.O.
```

- `ok` — compiled; `wall_s` is the cold build time.
- `T.O.` — hit the wall cap (`wall_s` = `CAP`).
- `fail` — errored (e.g. an earlier-failed dependency's olean is missing — same rule in both worlds).

`results/run_meta_<jobid>.txt` records host, CPU model, git commit, cap/jobs, and solver paths for
reproducibility.

## Notes / caveats

- **Hardware**: pinned to `EPYC_9634` (cpunode10/11) so both worlds run on identical silicon and the run is
  reproducible. `--exclusive` avoids noisy neighbors; `-j1` removes the core-count confound (measures total
  work, not parallel wall — conservative, since the monolith can't parallelize anyway).
- **Dependency failures cascade** (by design, both worlds): if a foundational prop times out, later props that
  import it also fail — recorded as `fail`, not deceptively fast. That's the intended "monolith is fragile"
  signal.
- This is the **first pass** (single run) to see the landscape and set the cap. A variance run (5×, medians)
  would reuse the same driver.
