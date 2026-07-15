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
MODE=""; BUDGET=50.00; MODEL=opus; END=48
while [ $# -gt 0 ]; do
  case "$1" in
    --ablated) MODE=ablated ;;
    --full)    MODE=full ;;
    --budget)  BUDGET="${2:?}"; shift ;;
    --model)   MODEL="${2:?}"; shift ;;
    --end)     END="${2:?}"; shift ;;
    *) echo "unknown arg: $1"; exit 1 ;;
  esac; shift
done
[ -z "$MODE" ] && { echo "usage: run_baseline.sh --ablated [--budget 50] [--model opus] [--end 48]"; exit 1; }

# ---- branch guard (the script is allowed to check git) ----
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
if [ "$MODE" = ablated ]; then
  [ "$branch" = ablation_branch ] || { echo "ABORT: --ablated must run on 'ablation_branch' (currently on '$branch')"; exit 1; }
else
  echo "ABORT: --full is not wired up yet (only --ablated works for now)"; exit 1
fi

OUT="$ABL/out/$MODE"; mkdir -p "$OUT"
echo "=== baseline run · mode=$MODE · branch=$branch · Book1 props 1..$END · \$$BUDGET/prop · model=$MODEL ==="

# ---- hide memory for the whole run (restore on any exit) ----
restore_mem() {
  if [ -d "$HIDDEN" ]; then
    [ -d "$MEMDIR" ] && mv "$MEMDIR" "${MEMDIR}.recreated_junk_$$"
    mv "$HIDDEN" "$MEMDIR" && echo "[memory restored]"
  fi
  rm -f "$OUT/_current.txt"
}
trap restore_mem EXIT
if [ -d "$MEMDIR" ]; then mv "$MEMDIR" "$HIDDEN" && echo "[memory hidden]"
else echo "!! memory dir not found ($MEMDIR) — aborting to avoid a leaked run"; exit 1; fi

# ---- grade (SAME for both arms): compiles + 0 sorry + map unchanged (texts/statement/claims) +
#      citations. Relaxed = drop the METHODOLOGY-only checks (bulk-tactic, backing-file, @assumption
#      annotation drift). Cheap checks first. ----
grade() { # $1 = Book1/PropNN
  local rel="$1" main="$LEP/$1/Main.lean" mod="${1//\//.}.Main"
  [ -f "$main" ] || return 1
  [ "$(grep -c 'sorry' "$main")" -eq 0 ] || return 1                                          # 0 sorry
  ( cd "$LEP" && python3 scripts/check_faithful.py --relaxed "$1/Main.lean" >/dev/null 2>&1 ) || return 1  # texts + citations + structure
  ( cd "$LEP" && python3 scripts/check_signatures.py "$1/Main.lean"          >/dev/null 2>&1 ) || return 1  # statement unchanged
  ( cd "$LEP" && python3 scripts/check_steps.py "$1/Main.lean"               >/dev/null 2>&1 ) || return 1  # claim types + @assumption/have types unchanged (map lock)
  ( cd "$LEP" && lake build "$mod"                                           >/dev/null 2>&1 ) || return 1  # compiles (last: slowest)
  return 0
}

# ---- run the agent on one prop (budget loop), archive, grade. Returns 0 = SUCCESS. ----
run_prop() { # $1 = NN (zero-padded)
  local nn="$1" rel="Book1/Prop$nn" pdir="$OUT/Prop$nn"; mkdir -p "$pdir"
  local cert="Prop$nn of Book1 that I was assigned to work on, is completely done. I certify it is faithful, compiles with no sorry, and is ready for review."
  local prompt="$rel/Main.lean (under LeanEuclidPlus/) is a Lean proof of Euclid's Book 1 Proposition ${nn#0}, with every step body left as ':= by sorry'. Fill in all the sorries so the file compiles and builds with NO sorry. Keep these UNCHANGED (do not rename, retype, move, or delete them): the theorem statement, each euclid_sentence's claim type '(stepN : …)', and the '-- @assumption (…)' comment lines. Cite any proposition Euclid cites (a proposition of the same number, or a variant of it, is fine). Do NOT use git. When it fully compiles with zero sorry, print on its OWN line EXACTLY this and nothing appended: $cert"
  local cont="Continue until $rel/Main.lean compiles with zero sorry. Do NOT use git. Only when fully done, print on its own line EXACTLY: $cert"

  echo "Prop$nn" > "$OUT/_current.txt"
  echo "--- Prop$nn: starting (\$$BUDGET budget) ---"
  git -C "$REPO" checkout HEAD -- "LeanEuclidPlus/$rel/Main.lean" 2>/dev/null   # every attempt starts from the clean committed map
  cd "$REPO"
  local spent=0 wall_ms=0 remaining="$BUDGET" out sid jsonl i=0
  out=$(claude -p "$prompt" --model "$MODEL" --permission-mode acceptEdits --output-format json --max-budget-usd "$remaining")
  echo "$out" > "$pdir/turn0.json"
  sid=$(echo "$out" | jq -r '.session_id')
  jsonl="$(find "$HOME/.claude/projects" -name "$sid.jsonl" 2>/dev/null | head -1)"
  while true; do
    local tc; tc=$(echo "$out" | jq -r '.total_cost_usd // 0')
    spent=$(awk "BEGIN{print $spent+$tc}"); remaining=$(awk "BEGIN{print $BUDGET-$spent}")
    wall_ms=$(awk "BEGIN{print $wall_ms + $(echo "$out"|jq -r '.duration_ms // 0')}")
    echo "    Prop$nn round $i: turn=\$$tc cumulative=\$$spent remaining=\$$remaining subtype=$(echo "$out"|jq -r '.subtype')"
    echo "$out" | jq -r '.result' | grep -qF "$cert" && break
    [ "$(echo "$out"|jq -r '.subtype')" = error_max_budget_usd ] && { echo "    (budget cut)"; break; }
    [ "$(awk "BEGIN{print ($remaining<=0.05)}")" = 1 ] && break
    i=$((i+1)); [ "$i" -gt 300 ] && { echo "    (safety backstop)"; break; }
    out=$(claude -p "$cont" --resume "$sid" --model "$MODEL" --permission-mode acceptEdits --output-format json --max-budget-usd "$remaining")
    echo "$out" > "$pdir/turn$i.json"
  done
  [ -n "${jsonl:-}" ] && cp "$jsonl" "$pdir/transcript.jsonl" 2>/dev/null
  local status=FAIL; grade "$rel" && status=SUCCESS
  printf 'prop: %s\nsession_id: %s\ntranscript: %s\ncost_usd: %s\nwall_sec: %s\nresult: %s\n' \
    "$rel" "$sid" "${jsonl:-<none>}" "$spent" "$(awk "BEGIN{print $wall_ms/1000}")" "$status" > "$pdir/result.txt"
  echo "=== Prop$nn -> $status  (\$$spent) ==="
  [ "$status" = SUCCESS ]
}

# ---- main loop: in order, skip done, STOP at first failure ----
last_done=0
for n in $(seq 1 "$END"); do
  nn=$(printf '%02d' "$n"); rel="Book1/Prop$nn"
  [ -f "$LEP/$rel/Main.lean" ] || { echo "skip Prop$nn (no Main.lean)"; continue; }
  if grade "$rel"; then echo "Prop$nn already done — skip"; last_done=$n; continue; fi
  if run_prop "$nn"; then
    last_done=$n
  else
    echo
    echo "=== STOP · first failure at Prop$nn · baseline depth = $last_done props (Prop01..Prop$(printf '%02d' "$last_done")) ==="
    exit 0
  fi
done
echo "=== reached Prop$(printf '%02d' "$END") with no failure · depth = $last_done ==="
