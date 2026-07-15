#!/usr/bin/env bash
# Live-monitor the baseline run — pretty-prints each turn, and AUTO-FOLLOWS the newest
# transcript as the runner advances from prop to prop. Shows which prop is active.
# READ-ONLY (tail -f); cannot interfere with the run. Run in a SECOND terminal.
#
# Usage:
#   bash 9_monitor.sh                # follows the ablated run
#   bash 9_monitor.sh full           # follows the full run
#   bash 9_monitor.sh <session-id>   # pin one specific session (no auto-follow)
set -uo pipefail
REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"
PROJ="$HOME/.claude/projects/${SLUG}"
ARG="${1:-ablated}"
CUR="$REPO/reproducable_experiments/ablation_study/out/$ARG/_current.txt"

render() { jq -rc --unbuffered '
  if .type=="assistant" then (.message.content[]? |
     if .type=="text" then "\n💬 "+.text
     elif .type=="tool_use" then "🔧 "+.name+"  "+((.input|tostring)[0:200]) else empty end)
  elif .type=="user" then (.message.content[]? |
     if (type=="object" and .type=="tool_result") then "   ↳ "+((.content|tostring)[0:240]) else empty end)
  else empty end'; }

tailpid=""
cleanup() { [ -n "$tailpid" ] && kill "$tailpid" 2>/dev/null; pkill -P $$ tail 2>/dev/null; }
trap 'cleanup; exit' INT TERM

# pinned single session?
if [ -f "$PROJ/$ARG.jsonl" ]; then
  echo "== pinned session $ARG =="; tail -n +1 -f "$PROJ/$ARG.jsonl" | render; exit 0
fi

echo "== monitoring '$ARG' run · auto-follows newest transcript · Ctrl-C to stop (read-only) =="
cur_f=""
while true; do
  f="$(ls -t "$PROJ"/*.jsonl 2>/dev/null | head -1)"
  if [ -n "$f" ] && [ "$f" != "$cur_f" ]; then
    cleanup; cur_f="$f"
    echo; echo "════════ now on: $(cat "$CUR" 2>/dev/null || echo '?')    ($(basename "$f")) ════════"
    ( tail -n +1 -f "$cur_f" | render ) & tailpid=$!
  fi
  sleep 3
done
