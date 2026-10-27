# LLM-oracle experiment — design notes

**Goal (rebuttal).** Show the *oracle role* in the faithfulness pipeline needs **no
per-proposition human judgment**: an LLM filling it drives the SAME full pipeline end to end
(split → map → assumptions → prove → wire), producing kernel-checked faithful artifacts. We then
grade those artifacts' quality (authors + a cross-family LLM judge — a SEPARATE, post-hoc step, not
in this harness). This directly answers the reviewers' "who is the oracle / how much hidden human
work / is it automatable" (Xq4R, enda, TEEJ).

**What is and isn't automated (the honest claim).** The domain knowledge — skills, `find.py`,
`Helpers/`, `euclid-figures` — is *fixed infrastructure authored once offline*, like a prover's
tactic library. It is held CONSTANT (identical to the human-oracle `full` runs). The experiment
automates the **runtime oracle**: the map-stage accept/reject and the fill-stage gap adjudication.
So the comparison is **same system, oracle = LLM vs oracle = human** — the oracle is the only
changed variable vs the gold `full` artifacts. We do NOT claim "LLM with zero human knowledge."

## Where it lives / what runs where

| | |
|---|---|
| harness (driver, submit, this doc, props, out/, leak_check, view_transcript) | `DNA/reproducable_experiments/oracle_experiment/` (MAIN checkout) |
| runs execute in | worktree `methodology_compare_worktrees/llm_oracle` @ branch `llm_oracle_branch` |
| blank/reset pin | `llm_oracle_branch` HEAD (committed Step-2 blank: every prop signature + `:= by sorry`) |
| methodology pin | byte-identical to `full_methodology_branch` @ `e072b931` (full, verbatim) |

The harness is deliberately **only in main, not in the worktree** — the worker (running in the
worktree) physically cannot read the driver/prompts/grader. Defense-in-depth: the worker prompt also
forbids reading `reproducable_experiments/` and using `git` (both AUTO-FAIL), exactly as the ablation.

## Isolation (reused verbatim from the ablation — all leak vectors already solved)

- **No gold anywhere to crib.** Step 2 blanked ALL 99 props + Book1Variants to signature + `sorry`,
  imports stripped to `SystemE`. Even if the worker or oracle reads around the repo, there is no
  answer to find.
- **Memory** keyed to git-common-dir = main repo (shared across worktrees); currently empty. Driver
  `rm -rf`'s it per run (throwaway, idempotent, parallel-safe) so no cross-prop note leaks in.
- **Git: enforced two ways.** Blocked — the worktree's committed `.claude/settings.json` already has
  `Bash(git:*)` and `Bash(git)` in `permissions.deny` (and denies the agent writing
  `step_signatures.json`/`assumption_tags.json`/`proposition_signatures.json`). Detected — the
  driver's outcome scans the transcript for any git token → AUTO-FAIL. git history is the one path to
  the gold, so this is the enforcement that matters.
- **Reaching outside the worktree (to crib gold from a sibling checkout): threat + post-hoc scan.**
  The worker prompt makes it an explicit AUTO-FAIL and says it's transcript-checked. Enforcement is
  `leak_check.py` (post-hoc, lives in the main checkout → the worker can't read it to game it): it
  flags any command / file-open / `<<<RUN>>>` that references a sibling gold tree
  (`{DNA,DNA-main,full,od_only,ablated}/LeanEuclidPlus`, `/autoform/DNA[-main]/`) or the harness, and
  with `--mark` flips that run's `result.txt` to FAIL. Honest limit: catches DIRECT references, not
  obfuscation (base64, or `cp` gold to /tmp then read /tmp) — true immunity needs an FS sandbox.
- **Headless on the subscription**: `unset ANTHROPIC_API_KEY`, `claude -p`, `--permission-mode
  acceptEdits`, budget cap, auto-continue, 12h watchdog, rate-limit retry, `<<<RUN>>>` long-command
  channel — all lifted from `run_comparison_experiment.sh`.

## The two roles

- **Worker** — the normal full-methodology agent, running in the worktree with all skills. Unlike
  the ablation (which started from a given map and only *filled*), the worker here also does the
  **map stage** from Euclid's English text. One persistent session across phases A and B.
- **Oracle** — a SEPARATE, answer-blind `claude -p`, **provably sandboxed yet System-E-literate**: it
  runs in a throwaway `/tmp` dir (outside any repo → no project `CLAUDE.md`/skills/memory → clean,
  unbiased) with **all tools disallowed** (`--disallowedTools Bash Read Edit Write …`), so it
  physically cannot read the gold. Everything it needs is passed **inline**: the vocab primer **plus
  the full System-E `Theory/` — sorts, relations, constructions, and inference AXIOMS (~36 KB, the
  real semantics a human oracle reads)** — then Euclid's proof text and the worker's (text, claim)
  pairs. So it judges against the actual axioms, not a thin summary, without any file access. Plain
  Claude on the subscription (cross-family is reserved for the post-hoc *judge*). Two gates, per the
  paper:
  1. **Map review** — after the worker prints `MAP_READY`: checks the exactly-two Oracle conditions
     from the paper's Table of Conditions — **Atomicity** (each `s_i` has a single assertion
     `assert(s_i)` with assumptions `assumptions(s_i)`) and **Atomic Faithfulness** (for all
     `a ∈ assumptions(s_i)`, `F(a)` is faithful, and `F(assert(s_i))` is faithful) → `{accept, reasons}`.
     Coverage/Order/Citation are Script-checked, Soundness is Lean — not the oracle's job.
  2. **Gap adjudication** — only when the worker prints `GAP_FLAG` during fill: decides whether a
     suspected Euclid gap is genuine → `{agree, note}`. (The paper's only fill-stage oracle touch.)

## Driver = a phase state-machine over one worker session

```
reset prop to blank  →  Phase A (worker: split+map)  ──MAP_READY──▶  ORACLE map-review
     ▲                                                                     │
     └──────────── reject: resume worker with reasons ◀────────────────────┤ (≤ MAX_MAP_ROUNDS)
                                                                 accept ▼
   check_steps.py --save  (freeze the approved map as the grade baseline)
                          assumptions.py  (mechanical, no LLM)
                                   │ exit 0 ───────────────────────────────────▶ Phase B
                                   │ exit≠0 ▶ state=assumptions_repair: worker runs /faithful-assumptions
                                   │           ──ASSUMP_FIXED──▶ assumptions.py --tag-only ──▶ Phase B
                                                                        ▼
            Phase B (worker: faithful-prove --drive, backing files)  ──GAP_FLAG──▶ ORACLE gap-adjudicate
                                   │  │                                 │                 │
                 GIVE UP ──▶ ORACLE intervene {resume│restart_fill│giveup}  ◀── resume with ruling
                 (fix bad map; only giveup ends the run)                 │
                                              ──FILL_COMPLETE (check_step --all exits 0)──▶
   Phase C (mechanical, NOT fed back): wire_main.py → lake build → check_faithful.sh (olean, focused)
                                     + check_backing + check_signatures + check_steps → grade
```

Sentinels the worker prints on their own line: `MAP_READY`, `FILL_COMPLETE`,
`GAP_FLAG: <locator> :: <why>`, and `GIVE UP`. The worker never wires Main (Phase C does).

**Worker GIVE UP → ORACLE intervention (only the oracle may truly end a run).** We know these props
are provable with the pipeline, so a worker give-up almost always means the oracle approved a *bad
map* (the paper's failure mode #2). So a give-up does NOT end the run — it invokes an
**intervention oracle** (an agent in the worktree that MAY edit the map). It investigates, fixes a
genuine map-stage mistake in `Main.lean`, and returns an action: `resume` (continue the same worker
session — map re-baselined + assumptions re-materialized if it edited past the map stage),
`restart_fill` (fresh fill session on the fixed map), or `giveup` (the ONLY true end — `status=
ORACLE_GAVEUP`). Capped at `MAX_INTERVENE` cycles (then `INCOMPLETE`). The intervention oracle's
transcript is captured for `leak_check` like every other agent.

## Grade (Phase C) — the hard, non-subjective result

`wire_main.py` (wires + builds Main) → `lake build` → then the **authoritative olean** gate
`check_faithful.sh Book{N}.Prop{NN}.Main` (= `faithful_export` + `check_faithful.py --olean --focus`:
book-aware text-tiling + order + citations, **focused on this prop** so the blanked siblings don't
interfere — this is the *thorough* check, not `--relaxed`) + `check_backing.py` (per-sentence backing
lemma) + `check_signatures.py` (statement unchanged) + `check_steps.py` (claim types unchanged vs the
oracle-approved `--save` baseline) + zero sorry. PASS = an LLM-oracle-driven, kernel-checked, faithful
artifact, stated without any judge; the subjective quality grading is the separate post-hoc step.

## Parallelism / build — PER-TASK worktree isolation

One prop per exclusive node (SLURM array, throttled), repeats sequential. **Unlike the ablation, we
do NOT share one worktree**: the full pipeline writes shared state per-prop —
`scripts/step_signatures.json` (`check_steps.py --save`) and `scripts/assumption_tags.json`
(`assumptions.py`), both read-modify-write merges — plus `.lake` and `.claude/settings.json`. Under a
shared worktree, concurrent props would race on these, and NFS file-locks don't work across nodes.

So `run_node.sbatch` gives each task its **own git worktree** (detached at `llm_oracle_branch`),
copies the warm `.lake` into it, runs the driver with `WORKTREE_OVERRIDE`, and tears the worktree down
on exit. This isolates every shared-state file. Memory is still shared (git-common-dir), but it's
empty and the per-run wipe is idempotent — harmless. `submit.sh` warms the base `.lake` once so each
task's copy starts warm (no SystemE/mathlib rebuild). git is already denied in the committed settings.json.

Tunable: full `cp -a` of `.lake` (~1.2 GB/task) is used for safety. If disk/copy-time is tight,
switch to hardlinks (`cp -al`) or symlink the read-only `.lake/packages` and copy only `.lake/build`.

## Metrics recorded per run (`out/<Book_Prop>/<run_id>/`)

`result.txt` (prop, status, stop_reason, costs, wall) + `metrics.json` (map oracle rounds, map
accepted?, each round's verdict JSON, gap flags + rulings, worker vs oracle cost split, grade
pass/fail + first failing check) + `grade.log` + `transcript.jsonl` + a snapshot of the produced
PropNN folder. One run each per prop (feasibility/existence demonstration, not a reliability number —
see rebuttal framing).

## Knobs to edit

Prompts (worker briefs A/B, the two oracle prompts) and config (budget, MAX_MAP_ROUNDS, models) live
at the top of `run_oracle_experiment.sh` under `*** EDIT HERE ***`. Oracle + worker both default to
`claude-opus-4-8`.
