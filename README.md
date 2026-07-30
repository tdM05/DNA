# Pistis — Code and Data Supplement

This package accompanies the paper on **faithful** formalization of Euclid's *Elements* proofs.
It contains the Lean artifacts, the pipeline (**Pistis**, whose fill stage is the
**OrderDecompose** search), and the experiment code/results behind the paper's claims.

> **Anonymized, reference package.** Absolute paths and usernames have been replaced with
> neutral placeholders (`/home/user`, …), so scripts document *what was run* rather than being
> turnkey. Reproducing the Lean build requires the toolchain in `LeanEuclidPlus/` (Lean 4
> `v4.8.0-rc2`, Z3, cvc5); the agent runs additionally require Claude Code + model access.

## Layout

| Path | What it is |
|------|-----------|
| `LeanEuclidPlus/` | The Lean project: **the faithful proof artifacts** (Books I–III, `Book*/Prop*/`), the System E theory (`SystemE/`), and the pipeline scripts (`scripts/`). |
| `LeanEuclidPlus/scripts/` | The **OrderDecompose** tooling: `check_step.py` (per-node SF/SP/P verification), `wire_main.py`, `assumptions.py` (assumption-gap detection), `find.py`, and the faithfulness checkers. |
| `.claude/` | The agent harness: `skills/` (the Map/Fill instructions the LLM follows) and `hooks/` (guards against rewriting the faithful structure / "cheating"). |
| `reproducable_experiments/human_eval/` | **RQ1** — the double-blind human study (response CSVs + survey app). |
| `reproducable_experiments/ablation_study/` | **RQ2** — the fill-stage ablation (Pistis vs. bare LLM). |
| `reproducable_experiments/compile_time/` | **RQ3** — compile-time benchmark vs. LeanEuclid. |
| `CLAUDE.md` | Full operator guide for the pipeline (the authoritative how-to). |

## Mapping to the paper's claims

- **Faithful artifacts** (Books I–III, Contribution 1) → `LeanEuclidPlus/Book1|Book2|Book3/Prop*/`.
  Each `Main.lean` carries the per-sentence `euclid_sentence` structure; `step*.lean` are the
  filled backing lemmas. Build a proposition with the `scripts/` checkers (see `CLAUDE.md`).
- **RQ1 (faithfulness: human study + LLM judge)** → `reproducable_experiments/human_eval/`
  holds the human-review response CSVs and the survey app; see its `README.md`.
- **RQ2 (fill-stage ablation)** → `reproducable_experiments/ablation_study/`. See its
  `runner/README.md` for the harness (two-worktree design, grading) and the verified finding
  that the bare LLM stalls on monolithic builds while Pistis decomposes and converges.
  Per-run outcomes are in `out/<arm>/<prop>/<run_id>/result.txt`; `export_paper_data.py`
  produces the paper's plots from those.
- **RQ3 (compile time)** → `reproducable_experiments/compile_time/` (`run_timing.sh`,
  `plot_results.ipynb`, `README.md`).
- **Gaps & refutations (RQ4)** → marked in the Lean source; grep `@euclid_gap`,
  `@assumption_gap`, and `@suppress_deps_check` under `LeanEuclidPlus/Book*/`.

Bulk agent transcripts are trimmed to a few representative matched pairs (see
`ablation_study/runner/README.md`); all participant data is anonymized to opaque reviewer codes.
