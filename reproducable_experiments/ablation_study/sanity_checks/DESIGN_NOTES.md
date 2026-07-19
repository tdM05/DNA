# Ablation study — design notes & resolved problems

Goal: compare **full** version (skills + scripts + memory) vs **naive** version (bare LLM)
at filling a premapped Euclid prop, headless. Binary outcome = `phase_c` passes.
Second input = book+prop; some Book 3 props not done → error out if invalid.

`Fixed` = we have a decided solution. `Checked location` = where empirically verified
(`nan` = decided but not yet run/implemented).

## Headless mechanics (empirically tested)

| Problem | Fixed | Solution (brief) | Checked location |
|---|---|---|---|
| Run headless on the Claude subscription (no API key) | ✅ | `unset ANTHROPIC_API_KEY` then `claude -p`. Uses the logged-in Pro/Max. | `1_test_headless.sh` |
| Save the transcript | ✅ | Auto `.jsonl` under `~/.claude/projects/...`; also redirect `--output-format json` to a file per turn. | `1_test_headless.sh` |
| Track cost as it goes | ✅ | Parse `total_cost_usd` from JSON. It is **per-turn**, so sum script-side for a global total. | `1_test_headless.sh`, `3_test_costcap.sh` |
| Cap the budget + detect the cut | ✅ | `--max-budget-usd <amt>`; on exceed → exit 1 + `is_error:true` + `subtype:error_max_budget_usd`. Pass remaining-global each call. | `3_test_costcap.sh` |
| LLM stops early ("want me to continue?") — no oracle | ✅ | Capture `session_id`; loop `claude -p "continue" --resume $sid` until the certification string appears (or budget/turn cap). | `2_test_autocontinue.sh` |
| Tool use / edits / scripts must not hang headless | ✅ | `--permission-mode acceptEdits` (allowlisted scripts run; skills, hooks, CLAUDE.md load same as interactive). | `4_test_tooluse.sh` |
| Cross-chat memory leakage into a run | ✅ | Move the whole project `memory/` dir aside during the naive run. Auth is a separate file (`.credentials.json`) → no reauth. Only user-global leak source (no user CLAUDE.md/skills/rules exist). | `5_test_memory_leak.sh` (run pending) |
| Memory swap = data loss / crash risk | ✅ | It's a **rename, not delete** → nothing is lost. Restore at end; `trap ... EXIT` + a `.REAL_MEMORY` marker make recovery unambiguous. | `5_test_memory_leak.sh` |
| Restore NESTS the real dir (Claude recreates empty `memory/` when hidden) | ✅ | Restore must **set aside** any recreated `memory/` first, then move the real one back — a plain `mv $HIDDEN $MEMDIR` nests it one level deep. | `5_test_memory_leak.sh` (fixed after 1st run) |
| Full arm pollutes real memory (writes new files) | ✅ | Optional: snapshot `memory/` before the full run, restore after, so runs are reproducible. Ignore if you don't care. | nan |
| Full + naive can't run at once (share one `memory/` dir) | ✅ | Serialize the two arms per prop — one needs memory present, the other hidden, in the same dir. | nan |

## Experiment design decisions

| Problem | Fixed | Solution (brief) | Checked location |
|---|---|---|---|
| Starting state must be identical + not leak the answer | ✅ | Use **premapped, not prefilled** props: both arms start from the same map (`euclid_sentence`s present, bodies `:= by sorry`). | nan |
| Other props could be cribbed / but deleting them breaks the build | ✅ | Keep every other prop as **signature + `:= by sorry`**: citations/imports still resolve, no proof content to copy. (Verify the grade requires zero-sorry on the **target only**, tolerating dep-sorry — normal Lean, sorry is a warning.) | nan |
| LLM cheats by weakening a claim to make sorry trivial | ✅ | Grade requires final `euclid_sentence` claims **+ signature byte-identical** to the given map (`check_steps`/`check_signatures` vs baseline). | nan |
| Completion signal vs the actual grade (keep separate) | ✅ | Loop only checks for the **exact certification string** the agent must emit; `phase_c` is the separate final grade run **once** at the end (the review-gate oracle), never inside the loop. The grade is **not** fed back to the agent (one-shot, no oracle). | nan |
| Grade must be uniform though arms differ (full uses backing files + wiring, naive inlines) | ✅ | Both must deliver a **built, zero-sorry `Main`** with claims/signature unchanged; grade = build + `check_faithful` + baseline diff. Full may run `wire_main.py` itself to reach that end-state. | nan |
| The one convention the naive arm still needs | ✅ | Tell both arms the **citation rule** (cite the proposition each sentence references); the map guarantees tiling/faithfulness. Strip only the methodology (skills/scripts/memory) from naive. | nan |
| Budget could bias one arm | ✅ | Same cap ($100) **both arms**; high enough that failures are capability, not truncation. Watch subscription rate limits on big batches. | nan |
| Git history leaks the finished proof | ✅ | Deny **git entirely** (not on allowlist) on **both** branches — must actively override the current hook that allows read-only git. | nan |

## Still to do
- Run `5_test_memory_leak.sh` to empirically confirm the memory rename severs recall.
- Build the naive branch (strip scripts/skills, minimal CLAUDE.md = task + citation rule, deny git).
- Write the naive task-brief prompt.
- Assemble the harness: memory-swap → run loop (budget guard + certification-string continue) → final `phase_c` grade → record success/fail (+ budget-cut).
- Pick the prop list.
