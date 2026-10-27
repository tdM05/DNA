# `od-only` — the full pipeline minus its three non-OrderDecompose components

Third arm of the fill-stage ablation. `ablated` and `od-only` are meant to differ by **exactly
OrderDecompose and its enforcement machinery** — same model, same harness, same map commit, same
grade, same wall clock, and, after the deletions below, the same absence of a lemma library, a
goal-shape catalog, and a declaration search tool.

The point is attribution: §4.3's `ablated` arm removes skills, scripts, hooks and persistent memory
*together*, so it compares a bundle against a bare agent. This arm isolates the one component the
paper credits.

## Where it lives

| | |
|---|---|
| branch | `od_only_branch` @ `13498a1a` |
| worktree | `methodology_compare_worktrees/od_only` |
| branched from | `full_methodology_branch` @ `e072b931` (byte-identical, then one commit of deletions) |
| map / reset pin | `MAP_REF_ODONLY="b98dd2b"` — shares the `mymethod` pin |
| previous attempt | `od_only_branch_v1` @ `d384c310` — superseded; carries the older `ABLATION_ARM.md` |

`git diff --shortstat e072b931 13498a1a` → **43 files changed, 34 insertions, 4435 deletions.**

## The three components under test

| # | component | what it is | why it is not OrderDecompose |
|---|---|---|---|
| 1 | `.claude/skills/euclid-figures/` | goal-shape → axiom-chain proving catalog (334 loc) | a lookup table consulted at `prove-euclid`'s P step; contains no ordering, recursion, or budget rule |
| 2 | `LeanEuclidPlus/Helpers/` | 7-module shared figure-lemma library, **19 lemmas**, 371 loc | pre-proved domain content, not a search procedure |
| 3 | `LeanEuclidPlus/scripts/find.py` | smart-grep over the declaration database (379 loc) | the "agentic tool" credited in CreateLemmas / CreateHypothesis |

Two satellites go with them, since nothing else uses either:

- `LeanEuclidPlus/scripts/bake_index.py` (349 loc) — `find.py`'s index backend
- `LeanEuclidPlus/tests/` (2854 loc) — the parse-only suite for `bake_index` / `find`; never invoked during a run

## Exactly which files were deleted (31)

**Component 1 — euclid-figures (1 file)**

```
.claude/skills/euclid-figures/SKILL.md
```

**Component 2 — Helpers (8 files)**

```
LeanEuclidPlus/Helpers.lean              (aggregator, 13 loc)
LeanEuclidPlus/Helpers/Angle.lean        ( 2 lemmas,  61 loc)
LeanEuclidPlus/Helpers/Area.lean         ( 1 lemma,   23 loc)
LeanEuclidPlus/Helpers/OffLine.lean      ( 8 lemmas, 108 loc)
LeanEuclidPlus/Helpers/Parallel.lean     ( 1 lemma,   27 loc)
LeanEuclidPlus/Helpers/Pasch.lean        ( 3 lemmas,  45 loc)
LeanEuclidPlus/Helpers/RightAngle.lean   ( 1 lemma,   27 loc)
LeanEuclidPlus/Helpers/SameSide.lean     ( 3 lemmas,  80 loc)
```

The `Helpers.lean` aggregator had to go too — it is nothing but `import Helpers.*` over the seven
submodules, so leaving it would be a dangling import.

**Component 3 — find.py and its index backend (2 files)**

```
LeanEuclidPlus/scripts/find.py
LeanEuclidPlus/scripts/bake_index.py
```

**Satellite — the parse-only test suite (20 files)**

```
LeanEuclidPlus/tests/README.md
LeanEuclidPlus/tests/conftest.py
LeanEuclidPlus/tests/fixtures/axiom_neg.lean
LeanEuclidPlus/tests/fixtures/construction_exists.lean
LeanEuclidPlus/tests/fixtures/helper_curried.lean
LeanEuclidPlus/tests/fixtures/prop_family.lean
LeanEuclidPlus/tests/fixtures/relations_min.lean
LeanEuclidPlus/tests/test_abbrev.py
LeanEuclidPlus/tests/test_assumptions.py
LeanEuclidPlus/tests/test_bake_row.py
LeanEuclidPlus/tests/test_citations.py
LeanEuclidPlus/tests/test_facts.py
LeanEuclidPlus/tests/test_find.py
LeanEuclidPlus/tests/test_freshness.py
LeanEuclidPlus/tests/test_placement.py
LeanEuclidPlus/tests/test_smell.py
LeanEuclidPlus/tests/test_split.py
LeanEuclidPlus/tests/test_status.py
LeanEuclidPlus/tests/test_step_order_hook.py
LeanEuclidPlus/tests/test_suppress_deps.py
```

## Which files were edited (12)

No algorithm text was changed. Ten of these only delete a pointer to something that no longer
exists — leaving them would make the agent repeatedly invoke a deleted tool and a nonexistent
import, handicapping the arm for a reason unrelated to the ablation. Two are build repairs.

| file | +/− | what changed |
|---|---|---|
| `.claude/skills/faithful-prove/SKILL.md` | +6 −53 | excised `THE LIBRARY EXCEPTION` block, the `Helpers/`+`find.py` branch of the decision tree, the `Helpers.*` carve-out in the import invariant, 2 trailing refs |
| `.claude/skills/prove-euclid/SKILL.md` | +11 −29 | dropped `⟨LIBRARY FIRST⟩` notes and the `Helpers/` lemma entries; 3 `find.py` signature lookups → read the theory files; 4 `euclid-figures` cross-refs. **All axiom chains and the pattern gallery are intact** |
| `CLAUDE.md` | +4 −16 | removed the `euclid-figures` paragraph, the `find.py` tool-hygiene bullet, the `find.py` superposition mention, `Helpers/` from the OldBook1 import list |
| `.claude/skills/faithful-map/SKILL.md` | +5 −5 | 3 `find.py` mentions in the reading policy |
| `.claude/skills/faithful-patterns/SKILL.md` | +2 −2 | `euclid-figures` analogy, `find.py` superposition lookup |
| `.claude/settings.json` | +0 −4 | allow-entries for `find.py` / `bake_index.py` |
| `.claude/hooks/bash_hygiene.py` | +4 −5 | `ALLOWED_SUMMARY`, `_BARE_ONLY_PY`, the python allowlist tuple |
| `LeanEuclidPlus/scripts/README.md` | +0 −10 | the two tool table rows and the `Tests` section |
| `LeanEuclidPlus/FAITHFUL.md` | +1 −1 | one `find.py` mention |
| `LeanEuclidPlus/Book2/WORKFLOW.md` | +1 −1 | one `Helpers.*` mention |
| **`LeanEuclidPlus/Book2.lean`** | +0 −5 | **build repair** — removed `import Helpers.{RightAngle,OffLine,SameSide,Area,Parallel}` |
| **`LeanEuclidPlus/lakefile.lean`** | +0 −3 | **build repair** — removed `lean_lib Helpers { }`, whose source dir no longer exists |

## What is unchanged

**OrderDecompose, in full.** `faithful-prove` and `prove-euclid` (the ordered loop, the recursive
SF/SP/P atom, the 30s cap); `.claude/hooks/step_order_hook.py` (denies writing `stepN` past the
frontier — a hard gate); `check_step.py`, `scaffold_step.py`, `wire_main.py`, `faithful_lib.py`;
every `euclid_sentence` map; the harness and its gates.

## Verified after the deletions

- `bash_hygiene.py`, `step_order_hook.py`, `faithful_lib.py` all compile; `settings.json` is valid JSON
- `faithful_lib.status_rows` still imports — the step-order hook's only dependency survived the cut
- step-order hook live-tested on a blank prop: writing `step3.lean` while `step1` is uncertified is
  **denied** with the in-order-discipline message; `step1.lean` and `Main.lean` are allowed
- zero remaining references to the deleted components in any auto-loaded file (`CLAUDE.md`, the
  skills, `settings.json`)
- starting state matches `full` exactly: **99 props blank, 0 proven, 0 stray step files**
- gates clear: GATE 1 branch guard, GATE 2 worktree lookup, GATE 2 driver parity
  (`run_comparison_experiment.sh` identical across all three arms, md5 `22cb9d9f…`)

**Not verified:** `lake build`. The two build repairs (`Book2.lean`, `lakefile.lean`) are checked by
inspection only. Build before trusting a run.

## Known-stale claim in the superseded doc

`od_only_branch_v1`'s `ABLATION_ARM.md` lists, under "What is UNCHANGED", that `bash_hygiene.py`
gates raw `lake build` so every build routes through `check_step.py`'s 30s wall. **That is not in
force.** `bash_hygiene.py` is registered as a hook in no settings file — not in the DNA repo, not in
any of the three worktrees, not user-global. It exists as a file and never runs.

Two consequences:

1. The 30s wall holds only when the agent chooses to go through `check_step.py`; raw `lake build` is
   not blocked.
2. `step_order_hook` is registered on `Write` and `Edit` only, so a step file written via Bash
   (`cat > step12.lean`) bypasses the frontier gate.

Both are **identical in `full` and `od-only`** (same `PreToolUse` matchers, same absent
registration), so the comparison stays internally valid and this is not a confound. It does mean the
sentence as written in the old doc is wrong and should not be repeated.
