# Ablation-study runner — how the comparison runs were produced

This is the harness that generated the results in `../out/`. It is included **as reference so
the methodology is inspectable**, not as a one-click script (it assumes the two-worktree
layout, SMT solvers, Lean toolchain, and headless model access described below).

- `run_comparison_experiment.sh` — the driver: one headless run of one proposition, one arm,
  then a single grade. **This one script drives both arms** (byte-identical in both worktrees,
  checked at startup), so the harness is identical and only the task prompt differs.
- `run_node.sbatch` / `submit.sh` — SLURM launch (one proposition per node, N repeats each).

## The comparison

Two ways of driving the **same** headless model on the **same** premapped proposition:

- **`--ablated`** — a bare LLM told to fill every `sorry` in the required per-sentence backing
  structure, but with **none of the pipeline tooling** (no skills, no order-decompose, no
  helper library).
- **`--my-method`** — the full pipeline (order-decompose).

Every run first resets the proposition to a pinned map-stage `Main.lean`: the faithful
sentence structure with all proof bodies left `:= by sorry`. Both arms start from that
identical blank-but-mapped proof; neither sees a filled solution.

## Two worktrees, run one arm at a time

Each arm runs in its **own git worktree on its own branch** (`ablation_branch` /
`full_methodology_branch`). Two worktrees are needed because the arms require **different
repo contents**: the ablated branch removes the pipeline tooling (the `scripts/`, hooks, and
skills) that the full method relies on, so the two cannot share one working tree. The results
go to one shared `../out/` outside both worktrees.

We also **never run the ablated and order-decompose arms at the same time**: the model's
project memory is keyed to the git repo root and shared across worktrees, so concurrent runs
could cross-contaminate. Memory is wiped before each run, and runs are executed one arm at a
time, so every run is independent.

## Grading and results

A single final grade (same for both arms, run once, never shown to the model): zero `sorry`,
faithfulness checks, per-sentence backing structure, unchanged signatures/claim types, and a
clean `lake build` within the cap. A 12 h wall marks an unfinished run `TIMEOUT`.

Each run's outcome is in `../out/<arm>/<prop>/<run_id>/result.txt` — this is the **authoritative
verdict**. The paper's plots come from `../export_paper_data.py`, which reads **only** those
`result.txt` files, so the numbers reproduce from the small files alone. The verbose
`grade.log` in each run folder is a transient trace of the grading subshell, not the verdict.

A few runs were **manually corrected** where the automated grade reported a failure caused by a
transient environment glitch, not by the proof. In each such case **we re-ran the build ourselves
and confirmed it compiles**, then set `result.txt` accordingly. For example, in
`out/ablated/Book1_Prop18_opus/20260720-214658-df632635/`, `grade.log` ends with
`timeout: failed to run command 'lake': No such file or directory` — `lake` was not on `PATH` in
that grading subshell, so the automated `lake build` step could not run. We manually rebuilt that
proposition, it compiled cleanly, and `result.txt` records the confirmed `SUCCESS`. When
`result.txt` and `grade.log` disagree, `result.txt` is the manually verified, authoritative value.

## What the transcripts show

**Ablated fails by building the whole proof at once.** A `lake build …Main` of the
undecomposed goal is one enormous SMT query that never terminates; it is still running when the
12 h wall fires (its `run<N>.log` is **0 bytes** — a build killed by the wall). With no
decomposition and no progress tracking, it keeps rewriting files and re-firing the same
monolithic build. **The full method decomposes** into small step lemmas built in fast scoped
batches and converges to `SUCCESS`.

To stay within the size limit we keep full `transcript.jsonl` files only for a few matched
pairs (both arms, all repeats); every other run keeps its small files so the record and plots
still reproduce.

| Proposition | Why kept |
|-------------|----------|
| **Book3/Prop11** | Strongest contrast: ablated hangs on the monolithic build (0-byte logs); full method succeeds. |
| **Book2/Prop03** | Same contrast, Book 2. |
| **Book1/Prop06** | Control: an easy proposition where **both** arms succeed — ablation fails on hard/large goals, not universally. |
