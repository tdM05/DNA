#!/usr/bin/env bash
# ============================================================================
# Sequential baseline runner over Book1. Runs the agent on each prop IN ORDER,
# STOPS at the first failure (the sound-prefix depth is the metric). Resumes
# from the last already-done prop. Each prop gets its own folder:
#   out/<mode>/PropNN/{transcript.jsonl, turn*.json, result.txt}
# result.txt records: prop, session_id, cost, result(SUCCESS/FAIL).
#
# Usage:
#   bash run_baseline.sh --ablated [--budget 50] [--model opus] [--end 48]
#   (--full is reserved; not wired up yet.)
# ============================================================================
set -uo pipefail
unset ANTHROPIC_API_KEY
set +u; source "$HOME/.venvs/leaneuclid/bin/activate"; set -u   # z3/cvc5 on PATH for lake build

REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
LEP="$REPO/LeanEuclidPlus"
ABL="$REPO/reproducable_experiments/ablation_study"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"
MEMDIR="$HOME/.claude/projects/${SLUG}/memory"
HIDDEN="${MEMDIR}.HIDDEN_baseline"

# ---- args ----
MODE=""; BUDGET=50.00; MODEL=opus; END=48; BOOK=1; PROPONLY=""
while [ $# -gt 0 ]; do
  case "$1" in
    --ablated) MODE=ablated ;;
    --full)    MODE=full ;;
    --budget)  BUDGET="${2:?}"; shift ;;
    --model)   MODEL="${2:?}"; shift ;;
    --end)     END="${2:?}"; shift ;;
    --book)    BOOK="${2:?}"; shift ;;
    --prop)    PROPONLY="${2:?}"; shift ;;     # run ONLY this one prop, e.g. --book 2 --prop 4
    *) echo "unknown arg: $1"; exit 1 ;;
  esac; shift
done
[ -z "$MODE" ] && { echo "usage: run_baseline.sh --ablated [--book N] [--prop NN] [--budget 50] [--model opus] [--end 48]"; exit 1; }

# ---- branch guard (the script is allowed to check git) ----
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
if [ "$MODE" = ablated ]; then
  [ "$branch" = ablation_branch ] || { echo "ABORT: --ablated must run on 'ablation_branch' (currently on '$branch')"; exit 1; }
else
  [ "$branch" = full_methodology_branch ] || { echo "ABORT: --full must run on 'full_methodology_branch' (currently on '$branch')"; exit 1; }
fi

OUT="$ABL/out/$MODE"; mkdir -p "$OUT"
if [ -n "$PROPONLY" ]; then
  echo "=== baseline run · mode=$MODE · branch=$branch · SINGLE Book$BOOK/Prop$(printf '%02d' "$PROPONLY") · \$$BUDGET · model=$MODEL ==="
else
  echo "=== baseline run · mode=$MODE · branch=$branch · Book$BOOK props 1..$END · \$$BUDGET/prop · model=$MODEL ==="
fi

# ---- hide memory for the whole run (restore on any exit, incl. Ctrl-C / kill) ----
HB=""   # background elapsed-heartbeat PID; killed on exit/cancel so it never outlives the run
restore_mem() {
  [ -n "$HB" ] && kill "$HB" 2>/dev/null
  if [ -d "$HIDDEN" ]; then
    [ -d "$MEMDIR" ] && mv "$MEMDIR" "${MEMDIR}.recreated_junk_$$"
    mv "$HIDDEN" "$MEMDIR" && echo "[memory restored]"
  fi
  rm -f "$OUT/_current.txt"
}
trap restore_mem EXIT   # fires on normal exit, Ctrl-C (SIGINT), and kill (SIGTERM) — so cancel stays clean
if [ "$MODE" = ablated ]; then
  if [ -d "$MEMDIR" ]; then mv "$MEMDIR" "$HIDDEN" && echo "[memory hidden]"
  else echo "!! memory dir not found ($MEMDIR) — aborting to avoid a leaked run"; exit 1; fi
else
  echo "[--full: methodology memory KEPT visible]"   # the full arm USES the memory/skills — do not hide
fi

# ---- grade (SAME for both arms): compiles + 0 sorry + map unchanged (texts/statement/claims) +
#      citations. Relaxed = drop the METHODOLOGY-only checks (bulk-tactic, backing-file, @assumption
#      annotation drift). Cheap checks first. ----
grade() { # $1 = Book1/PropNN
  local rel="$1" main="$LEP/$1/Main.lean" mod="${1//\//.}.Main"
  [ -f "$main" ] || return 1
  [ "$(grep -c 'sorry' "$main")" -eq 0 ] || return 1                                          # 0 sorry
  ( cd "$LEP" && python3 scripts/check_faithful.py --relaxed "$1/Main.lean" >/dev/null 2>&1 ) || return 1  # texts + citations + structure
  ( cd "$LEP" && python3 scripts/check_signatures.py "$1/Main.lean"          >/dev/null 2>&1 ) || return 1  # statement unchanged
  ( cd "$LEP" && python3 scripts/check_steps.py --relaxed "$1/Main.lean"     >/dev/null 2>&1 ) || return 1  # claim types + @assumption types unchanged (map lock; --relaxed = regex, tolerates hand-written bodies)
  ( cd "$LEP" && timeout 3600 lake build "$mod"                              >/dev/null 2>&1 ) || return 1  # compiles within 1h (generous termination bound, NOT a tuned threshold; identical for both arms)
  return 0
}

# ---- write/refresh result.txt (reads run_prop's locals via bash dynamic scope). $1 = status.
#      Written EARLY (as soon as session_id is known) and refreshed each round, so the session_id +
#      live cost/wall are visible WHILE the prop runs, not only at the end. ----
write_result() {
  printf 'prop: %s\nsession_id: %s\ntranscript: %s\ncost_usd: %s\nwall_sec: %s\ncompile_sec: %s\nresult: %s\n' \
    "$rel" "${sid:-<pending>}" "${jsonl:-<none>}" "${spent:-0}" "$(awk "BEGIN{print ${wall_ms:-0}/1000}")" "${grade_sec:-<pending>}" "$1" \
    > "$pdir/result.txt"
}

# ---- run the agent on one prop (budget loop), archive, grade. Returns 0 = SUCCESS. ----
run_prop() { # $1 = NN (zero-padded)
  local nn="$1" rel="Book${BOOK}/Prop$nn"
  local plabel="Prop$nn"; [ "$BOOK" != 1 ] && plabel="Book${BOOK}_Prop$nn"
  plabel="${plabel}_${MODEL}"                         # keep per-model results separate (haiku/sonnet/opus)
  local pdir="$OUT/$plabel"; rm -rf "$pdir"; mkdir -p "$pdir"
  local cert="Prop$nn of Book${BOOK} that I was assigned to work on, is completely done. I certify it is faithful, compiles with no sorry, and is ready for review."
  local prompt cont
  if [ "$MODE" = full ]; then
    # FULL methodology: use the faithful pipeline / skills, prove AND wire.
    prompt="$rel/Main.lean (under LeanEuclidPlus/) has been reset to a premapped-but-UNPROVEN state: it holds the faithful euclid_sentence map with every body ':= by sorry', and the backing stepN.lean files were deleted. The pipeline scripts live in LeanEuclidPlus/scripts, so cd into LeanEuclidPlus and run them from there (e.g. 'python3 scripts/check_step.py $rel ...'). Fully prove AND WIRE it using the faithful pipeline (your prove-euclid / faithful-prove skills) end to end so Main compiles with NO sorry. Do NOT use git. When it is completely done and wired, print on its OWN line EXACTLY this and nothing appended: $cert"
    cont="Continue until $rel is completely proven AND wired (Main compiles, zero sorry). Do NOT use git. Only when fully done, print on its own line EXACTLY: $cert"
  else
    # ABLATED baseline: naive, any tactic, keep the map unchanged.
    prompt="$rel/Main.lean (under LeanEuclidPlus/) is a Lean proof of Euclid's Book ${BOOK} Proposition ${nn#0}, with every step body left as ':= by sorry'. Fill in all the sorries so the file compiles and builds with NO sorry. Keep these UNCHANGED (do not rename, retype, move, or delete them): the theorem statement, each euclid_sentence's claim type '(stepN : …)', and the '-- @assumption (…)' comment lines. Cite any proposition Euclid cites (a proposition of the same number, or a variant of it, is fine). Do NOT use git. When it fully compiles with zero sorry, print on its OWN line EXACTLY this and nothing appended: $cert"
    cont="Continue until $rel/Main.lean compiles with zero sorry. Do NOT use git. Only when fully done, print on its own line EXACTLY: $cert"
  fi

  echo "--- $rel: starting (\$$BUDGET budget · no time limit) ---"
  git -C "$REPO" checkout HEAD -- "LeanEuclidPlus/$rel/Main.lean" \
    || { echo "ABORT $rel: could not reset to its committed map"; return 1; }   # start each attempt from map
  grep -q 'sorry' "$LEP/$rel/Main.lean" \
    || { echo "ABORT $rel: HEAD's copy has NO sorry — committed as a full proof, not a map. Refusing to re-attempt it."; return 1; }
  cd "$REPO" || { echo "ABORT $rel: cannot cd to $REPO"; return 1; }
  # Pre-generate a FRESH, UNIQUE session id so the id AND its transcript path are known from t=0 — written
  # into _current.txt/result.txt immediately and passed to claude via --session-id. Regenerate on the
  # (astronomically-unlikely) chance the uuid already has a transcript on disk, so we can never collide.
  local PROJ="$HOME/.claude/projects/${SLUG}"
  local sid jsonl
  sid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
  while [ -e "$PROJ/$sid.jsonl" ]; do sid="$(python3 -c 'import uuid;print(uuid.uuid4())')"; done
  jsonl="$PROJ/$sid.jsonl"
  local t0; t0=$(date +%s)
  # heartbeat → _current.txt: the (pre-known) session id + transcript path + elapsed, from t=0.
  ( while :; do e=$(( $(date +%s) - t0 ))
      printf '%s  session=%s  transcript=%s  elapsed=%dm%02ds  (started %s · Ctrl-C to cancel)\n' \
        "$rel" "$sid" "$jsonl" $((e/60)) $((e%60)) "$(date -d @"$t0" +%H:%M:%S)" > "$OUT/_current.txt"
      sleep 15; done ) &
  HB=$!
  local spent=0 wall_ms=0 remaining="$BUDGET" out i=0 grade_sec=""
  write_result RUNNING                       # result.txt carries the session_id + transcript from t=0
  out=$(claude -p "$prompt" --model "$MODEL" --session-id "$sid" --permission-mode acceptEdits --output-format json --max-budget-usd "$remaining")
  echo "$out" > "$pdir/turn0.json"
  while true; do
    local tc; tc=$(echo "$out" | jq -r '.total_cost_usd // 0')
    spent=$(awk "BEGIN{print $spent+$tc}"); remaining=$(awk "BEGIN{print $BUDGET-$spent}")
    wall_ms=$(awk "BEGIN{print $wall_ms + $(echo "$out"|jq -r '.duration_ms // 0')}")
    write_result RUNNING                     # refresh live cost/wall each round
    echo "    $rel round $i: turn=\$$tc cumulative=\$$spent remaining=\$$remaining subtype=$(echo "$out"|jq -r '.subtype')"
    echo "$out" | jq -r '.result' | grep -qF "$cert" && break
    [ "$(echo "$out"|jq -r '.subtype')" = error_max_budget_usd ] && { echo "    (budget cut)"; break; }
    [ "$(awk "BEGIN{print ($remaining<=0.05)}")" = 1 ] && break
    i=$((i+1)); [ "$i" -gt 300 ] && { echo "    (safety backstop)"; break; }
    out=$(claude -p "$cont" --resume "$sid" --model "$MODEL" --permission-mode acceptEdits --output-format json --max-budget-usd "$remaining")
    echo "$out" > "$pdir/turn$i.json"
  done
  kill "$HB" 2>/dev/null; HB=""
  [ -n "${jsonl:-}" ] && cp "$jsonl" "$pdir/transcript.jsonl" 2>/dev/null
  local status=FAIL gt; gt=$(date +%s)                # time the full grade (all checks + lake build)
  grade "$rel" && status=SUCCESS
  grade_sec=$(( $(date +%s) - gt ))                   # compile+checks wall seconds → result.txt
  write_result "$status"
  echo "=== $rel -> $status  (\$$spent · $(( ($(date +%s)-t0)/60 ))m wall) ==="
  [ "$status" = SUCCESS ]
}

# ---- single-prop mode: ALWAYS a fresh attempt. run_prop resets the prop to its map first, so we never
#      grade (or slowly re-build) leftover working-tree state from a prior/interrupted run. ----
if [ -n "$PROPONLY" ]; then
  nn=$(printf '%02d' "$PROPONLY"); rel="Book${BOOK}/Prop$nn"
  [ -f "$LEP/$rel/Main.lean" ] || { echo "no such prop: $rel/Main.lean"; exit 1; }
  if run_prop "$nn"; then echo "=== $rel : SUCCESS ==="; else echo "=== $rel : FAIL ==="; fi
  exit 0
fi

# ---- main loop (Book$BOOK, in order): skip done, STOP at first failure ----
last_done=0
for n in $(seq 1 "$END"); do
  nn=$(printf '%02d' "$n"); rel="Book${BOOK}/Prop$nn"
  plabel="Prop$nn"; [ "$BOOK" != 1 ] && plabel="Book${BOOK}_Prop$nn"
  [ -f "$LEP/$rel/Main.lean" ] || { echo "skip $rel (no Main.lean)"; continue; }
  if grade "$rel"; then
    echo "$rel already done — skip"; last_done=$n
    [ -f "$OUT/$plabel/result.txt" ] && sed -i 's/^result: .*/result: SUCCESS/' "$OUT/$plabel/result.txt"  # keep a prior run's verdict honest
    continue
  fi
  if run_prop "$nn"; then
    last_done=$n
  else
    echo
    echo "=== STOP · first failure at $rel · depth = $last_done props ==="
    exit 0
  fi
done
echo "=== reached Book$BOOK/Prop$(printf '%02d' "$END") with no failure · depth = $last_done ==="
