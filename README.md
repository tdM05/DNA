# Pistis — Code and Data Supplement

This package accompanies the paper on **faithful** formalization of Euclid's *Elements* proofs.
It contains the Lean artifacts, the pipeline (**Pistis**, whose fill stage is the
**OrderDecompose** search), and the experiment code/results behind the paper's claims.

> **Anonymized package.** Absolute paths and usernames are replaced with neutral placeholders
> (`/home/user`, …).

## Getting started

**1. Lean toolchain + solvers.** Install [`elan`](https://github.com/leanprover/elan) (it reads
`LeanEuclidF/lean-toolchain` and pulls Lean `v4.8.0-rc2` automatically), and install the SMT
solvers **Z3** `4.15.4` ([release](https://github.com/Z3Prover/z3/releases/tag/z3-4.15.4)) and
**cvc5** `1.3.4` ([release](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.4)) so both are on
`PATH` (these are the exact solver versions used for all reported results), plus the wrapper the
Lean SMT integration actually invokes:
```bash
pip install z3-solver==4.15.4     # provides the `z3` binary
pip install smt-portfolio         # REQUIRED: the `smt-portfolio` dispatcher the build calls (not z3/cvc5 directly)
# cvc5: download the 1.3.4 Linux static binary from the release above, chmod +x, put on PATH
```
`smt-portfolio` must find `z3` and `cvc5` on `PATH`. Without it the build fails with
`could not execute external process 'smt-portfolio'`.

**2. Build System E and a proof (verifies the artifacts):**
```bash
cd LeanEuclidF
lake exe cache get                 # fetch the prebuilt mathlib cache
lake build SystemE                 # compile the System E theory (~minutes)
lake build Book1.Prop06.Main       # one faithful proof, end-to-end
# lake build Book1 Book2 Book3     # everything (long)
```

**3. Python (only for plots + running the pipeline live).** The checker/pipeline scripts and the
survey server use just the standard library. A small venv is needed only to regenerate the RQ2/RQ3
plots from the shipped CSVs:
```bash
python3 -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt
```
(Driving the agent pipeline live additionally needs `anthropic` + Claude Code; not required to
inspect artifacts, run the checkers, or regenerate plots.)

**4. Inspect the pipeline without building.** From `LeanEuclidF/`:
`python3 scripts/find.py --concludes "onCircle"` (search the fact DB),
`python3 scripts/check_faithful.py Book1/Prop01/Main.lean` (faithfulness check on a proof).

## Layout

| Path | What it is |
|------|-----------|
| `LeanEuclidF/` | The Lean project: **the faithful proof artifacts** (Books I–III, `Book*/Prop*/`), the System E theory (`SystemE/`), and the pipeline scripts (`scripts/`). |
| `LeanEuclidF/scripts/` | The **OrderDecompose** tooling: `check_step.py` (per-node SF/SP/P verification), `wire_main.py`, `assumptions.py` (assumption-gap detection), `find.py`, and the faithfulness checkers. |
| `.claude/` | The agent harness: `skills/` (the LLM's instructions for each pipeline stage — `faithful-split`/`faithful-map`/`faithful-signature` for the Map stage, `faithful-prove`/`prove-euclid` for the OrderDecompose fill stage, `faithful-assumptions` for the assumption phase) and `hooks/` (`step_order_hook.py` enforces OrderDecompose's in-order iteration; `bash_hygiene.py` blocks shortcuts/"cheating"). |
| `reproducable_experiments/human_eval/` | **RQ1** — the double-blind human study (response CSVs + survey app). |
| `reproducable_experiments/ablation_study/` | **RQ2** — the fill-stage ablation (Pistis vs. bare LLM). |
| `reproducable_experiments/compile_time/` | **RQ3** — compile-time benchmark vs. LeanEuclid. |
| `diagrams/` | Generator for the interactive proof-map visualizer (see `diagrams/README.md`). A ready-to-open `map.html` is **pre-generated in every `LeanEuclidF/Book*/Prop*/` folder** — open one in a browser to see that proposition's faithful sentence↔step map. |
| `CLAUDE.md` | The project instructions the coding agent (Claude Code). |

## Mapping to the paper's claims

- **Faithful artifacts** (Books I–III, Contribution 1) → `LeanEuclidF/Book1|Book2|Book3/Prop*/`.
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
- **Gaps & refutations (RQ4)** → **gaps** are marked in the Lean source: grep `@euclid_gap`,
  `@assumption_gap`, and `@suppress_deps_check` under `LeanEuclidF/Book*/`.
  **Accept / refute examples** live in `LeanEuclidF/accept_refute/1.5/` (Prop I.5): `refute_typeA_*`
  and `refute_typeB` are the two refutation forms, `accept/` is an *alternative* NL proof (a different
  proof of I.5 from Euclid's own) that the method accepts, and `accept_assump_gap/` is an accepted
  proof that still carries an assumption gap. The accept/refute notions are defined in the paper's
  Methodology section ("Acceptance, Refute, and Gaps") and analyzed qualitatively in RQ4
  ("Qual. Analysis of Refutations and Gaps"); the appendix section "Further Refutation Examples"
  walks through these exact folders.

## Source code ↔ paper correspondence for OrderDecompose

The new-method source implements the **OrderDecompose** algorithm (paper Algorithm 1) and the
faithfulness conditions (paper Table 1). Each file carries an explanatory module docstring; the
per-file role in the method is tabulated in the appendix (**Agent Tools** and **Verification &
Infrastructure Scripts** tables). The key correspondences:

| Source file | Paper reference |
|-------------|-----------------|
| `LeanEuclidF/scripts/check_step.py` | Runs the three per-step checks of OrderDecompose (Alg. 1): **SF** = *sufficient* (the step's claim, backing `sorry`, still closes its container — Alg. line 18), **SP** = *suppliable* (every hypothesis it needs is already in the parent context, `InContext` — Alg. lines 5/19; this enforces the **Order** condition), **P** = *provable* (the leaf lemma builds isolated with zero `sorry`, `Decomp` — Alg. line 6; enforces **Soundness**). `--drive`/`--all` run this bottom-up over the whole proof in source order. |
| `LeanEuclidF/scripts/find.py` | Backs `CreateHypothesis` / `CreateLemmas` (Alg. 1) and citation-dependency (Citation condition). |
| `LeanEuclidF/scripts/scaffold_step.py` | `CreateHypothesis` skeleton emitter (Alg. 1). |
| `LeanEuclidF/scripts/assumptions.py` | Assumption-gap tagging stage (Methodology; appendix tactic-ladder table). |
| `LeanEuclidF/scripts/check_faithful.py`, `check_steps.py`, `check_signatures.py` | Enforce Coverage / Citation / claim-type + signature immutability (Table 1). |
| `.claude/skills/faithful-*` | The Map and Fill stages (Methodology). |
| `.claude/hooks/step_order_hook.py` | Hard-enforces the in-order iteration of OrderDecompose (Alg. 1, line 1). |

Bulk agent transcripts are trimmed to a few representative matched pairs (see
`ablation_study/runner/README.md`); all participant data is anonymized to opaque reviewer codes.

## Built on LeanEuclid and System E

This package builds on **LeanEuclid** and its Lean implementation of the **System E** formalism for
Euclidean geometry (which uses SMT solvers for diagrammatic reasoning). `LeanEuclidF/SystemE/` is
the System E implementation, carried over with additions; the prior work faithfully formalized
**Book I** of the *Elements*, and this package extends the effort to **Books I–III** and replaces
hand-formalization with the automated, oracle-guided **Pistis** pipeline (the `Book*/` proofs and the
`scripts/` + `.claude/` tooling). See the main paper for full citations and comparison.
