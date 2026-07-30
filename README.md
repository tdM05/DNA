# Pistis — Code and Data Supplement

This package accompanies the paper on **faithful** formalization of Euclid's *Elements* proofs.
It contains the Lean artifacts, the pipeline (**Pistis**, whose fill stage is the
**OrderDecompose** search), and the experiment code/results behind the paper's claims.

> **Anonymized, reference package.** Absolute paths and usernames have been replaced with
> neutral placeholders (`/home/user`, …), so scripts document *what was run* rather than being
> turnkey. Reproducing the Lean build requires the toolchain in `LeanEuclidPlus/` (Lean 4
> `v4.8.0-rc2`, Z3, cvc5); the agent runs additionally require Claude Code + model access.

## Getting started

**1. Lean toolchain + solvers.** Install [`elan`](https://github.com/leanprover/elan) (it reads
`LeanEuclidPlus/lean-toolchain` and pulls Lean `v4.8.0-rc2` automatically), and install **Z3**
(4.15.4) and **cvc5** (1.3.4) so both are on `PATH`. See `LeanEuclidPlus/README.md` for the
upstream setup notes.

**2. Build System E and a proof (verifies the artifacts):**
```bash
cd LeanEuclidPlus
lake exe cache get                 # fetch the prebuilt mathlib cache
lake build SystemE                 # compile the System E theory (~minutes)
lake build Book1.Prop06.Main       # one faithful proof, end-to-end
# lake build Book Book2 Book3      # everything (long)
```

**3. Python (only for plots + running the pipeline live).** The checker/pipeline scripts and the
survey server use just the standard library. A small venv is needed only to regenerate the RQ2/RQ3
plots from the shipped CSVs:
```bash
python3 -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt    # matplotlib, numpy, pandas
```
(`requirements.lock.txt` is the full original-environment freeze, kept for reference only — not
needed for reproduction. Driving the agent live additionally needs `anthropic` + Claude Code.)

**4. Inspect the pipeline without building.** From `LeanEuclidPlus/`:
`python3 scripts/find.py --concludes "onCircle"` (search the fact DB),
`python3 scripts/check_faithful.py --split Book1/Prop01` (structural faithfulness check).

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

## Source code ↔ paper correspondence

The new-method source implements the **OrderDecompose** algorithm (paper Algorithm 1) and the
faithfulness conditions (paper Table 1). Each file carries an explanatory module docstring; the
per-file role in the method is tabulated in the appendix (**Agent Tools** and **Verification &
Infrastructure Scripts** tables). The key correspondences:

| Source file | Paper reference |
|-------------|-----------------|
| `LeanEuclidPlus/scripts/check_step.py` | The SF/SP/P checks and in-order `--drive`/`--all` audit — OrderDecompose (Alg. 1, lines 5/16/18/20); enforces Order + Soundness. |
| `LeanEuclidPlus/scripts/find.py` | Backs `CreateHypothesis` / `CreateLemmas` (Alg. 1) and citation-dependency (Citation condition). |
| `LeanEuclidPlus/scripts/scaffold_step.py` | `CreateHypothesis` skeleton emitter (Alg. 1). |
| `LeanEuclidPlus/scripts/assumptions.py` | Assumption-gap tagging stage (Methodology §; appendix tactic-ladder table). |
| `LeanEuclidPlus/scripts/check_faithful.py`, `check_steps.py`, `check_signatures.py` | Enforce Coverage / Citation / claim-type + signature immutability (Table 1). |
| `.claude/skills/faithful-*` | The Map and Fill stages (Methodology §). |
| `.claude/hooks/step_order_hook.py` | Hard-enforces the in-order iteration of OrderDecompose (Alg. 1, line 1). |

Bulk agent transcripts are trimmed to a few representative matched pairs (see
`ablation_study/runner/README.md`); all participant data is anonymized to opaque reviewer codes.
