# Compile-time benchmark: `naive_llm` vs `my_method` (ordered decomposition)

Measures, **per proposition**, the wall-clock time to compile that proposition *from cold* under two
proof-production methods, for the 5 props in the fill-comparison study:

| prop | Book / target |
|------|---------------|
| 1.1  | `Book1.Prop01.Main` |
| 1.26 | `Book1.Prop26.Main` |
| 1.43 | `Book1.Prop43.Main` |
| 1.47 | `Book1.Prop47.Main` |
| 3.33 | `Book3.Prop33.Main` |

- **naive** = the un-forced ("naive LLM") attempt — a single monolithic `Book<N>/PropNN/Main.lean`.
  Lives in the **ablated** worktree
  (`methodology_compare_worktrees/ablated/LeanEuclidPlus`, branch `ablation_branch`).
- **mine** = the ordered-decomposition method — `Main.lean` + its `stepK.lean` backing files.
  Lives in the **full** worktree
  (`methodology_compare_worktrees/full/LeanEuclidPlus`, branch `full_methodology_branch`).

Both prove the **same** `proposition_N` under the **same** lake target `Book<N>.PropNN.Main`; only the
proof structure differs. This is the direct analog of the `../compile_time` Book1-vs-OldBook1 benchmark.

**Fair-comparison guarantee.** The two worktrees share a **byte-identical `SystemE/`** (verified with
`diff -rq`), the same uncapped SMT (`systemE.solverTime = 100000` in `SystemE/Meta/Smt/Solver.lean`), the same lake
default parallelism, the same wall cap, and the same exclusive `EPYC_9634` node. So the only variable
is the proof's structure.

## Protocol

Per world, symmetric and clean (mirrors `../compile_time`):

1. `rm -rf <root>/.lake/build` — wipe **all** our built oleans (SystemE + every Euclid lib) for that
   worktree. Does **not** touch `.lake/packages/` (Mathlib), so Mathlib is never rebuilt.
2. `lake build SystemE` — build the shared framework once, **untimed** (reuses cached Mathlib).
3. Time each of the 5 targets cold, ascending, one at a time: `timeout $CAP lake build <target>`.
   Building `Main` transitively compiles that prop's whole cone (for **mine**, all its `stepK` files;
   for both, any cited props), so the single target captures the full cost.

Then repeat 1–3 for the other world → both start from an identical clean state. **Clearing before each
method is the point** — it guarantees neither method reuses the other's cached oleans.

## Run

Interactively (what you're doing — one exclusive CPU node):

```bash
srun --partition=cpunodes --constraint=EPYC_9634 --exclusive --nodes=1 --time=1-00:00:00 --pty bash
export PATH="/u/taddmao/.venvs/leaneuclid/bin:$PATH"      # z3, cvc5
bash /u/taddmao/code/autoform/DNA/reproducable_experiments/OD_vs_naive_comp_time/run_timing.sh
```

or batched:

```bash
sbatch /u/taddmao/code/autoform/DNA/reproducable_experiments/OD_vs_naive_comp_time/submit.sbatch
```

Tunables (env): `CAP` = per-prop wall seconds (default `3600`), `NUM_RUNS` (default `5`). (This `lake` has
no `-j` flag, so builds use lake's default parallelism — same as `../compile_time`.)

## Output

Each run writes `results/run<id>_<stamp>/`:

```
naive.csv    # 5 rows: target,wall_s,status   (ablated / monolithic)
mine.csv     # 5 rows: target,wall_s,status   (full / ordered decomposition)
build.log    # full lake output for both worlds
meta.txt     # run#, host, cap/jobs, both worktree git HEADs, prop list
```

CSV rows:

```
target,wall_s,status
Book1.Prop01.Main,4.31,ok
Book3.Prop33.Main,3600,T.O.
```

`ok` = compiled (`wall_s` = cold build time); `T.O.` = hit the wall cap; `fail` = errored.

## ⚠ Interpretation caveat

A compile-time number is only comparable **between two proofs that both actually compile to a valid,
`sorry`-free proof of the same theorem**. Before reporting, confirm each `naive.csv` / `mine.csv` row is
`ok` **and** that the corresponding `Main.lean` is `sorry`-free — a `naive` prop that builds only because
it still contains a `sorry` (a warning, not an error → status `ok`) is *not* a valid proof, so its
"compile time" is not a like-for-like measurement. Note per-prop whether each method produced a complete
proof; a cheaper compile of an incomplete proof is not a win.
