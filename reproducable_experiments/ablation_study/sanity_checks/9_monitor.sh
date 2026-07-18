#!/usr/bin/env bash
# Read-only live view of a run session: streams the transcript AND prints a stats line every 15s.
# NO persistent-tail leak (cleanup trap reaps children on any exit). Run in a second terminal.
#   bash 9_monitor.sh <session-id>   # a specific session (id with or without .jsonl)
#   bash 9_monitor.sh                # current ablated run (transcript from out/ablated/_current.txt)
set -uo pipefail
REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"
PROJ="$HOME/.claude/projects/${SLUG}"
OUT="$REPO/reproducable_experiments/ablation_study/out/ablated"

render() { jq -rc --unbuffered '
  if .type=="assistant" then (.message.content[]? |
     if .type=="text" then "\n💬 "+.text
     elif .type=="tool_use" then "🔧 "+.name+"  "+((.input|tostring)[0:200]) else empty end)
  elif .type=="user" then (.message.content[]? |
     if (type=="object" and .type=="tool_result") then "   ↳ "+((.content|tostring)[0:240]) else empty end)
  else empty end'; }

# ALWAYS reap our children (tail + stats loop) on exit — Ctrl-C, kill, terminal close.
# THIS is what stops leaked `tail -f` from piling up and exhausting inotify (the old bug).
cleanup() { pkill -P $$ 2>/dev/null; }
trap cleanup EXIT INT TERM HUP

# resolve the transcript to follow
arg="${1:-}"
if [ -n "$arg" ] && [ "$arg" != "ablated" ] && [ "$arg" != "full" ]; then
  f="$PROJ/${arg%.jsonl}.jsonl"
else
  f="$(sed -n 's/.*transcript=\([^ ]*\).*/\1/p' "$OUT/_current.txt" 2>/dev/null | head -1)"
fi
[ -n "${f:-}" ] && [ -f "$f" ] || { echo "no such transcript — pass a session id: bash 9_monitor.sh <id>"; exit 1; }
sid="$(basename "$f" .jsonl)"

# one stats line: transcript activity + cost. Exact rounds/cost come from result.txt once a round
# returns; before that, ~cost is estimated from token usage (Opus rates: in $15, out $75, cache-write
# $18.75, cache-read $1.5 per Mtok) — labelled (est) because it's not the billed figure.
stats_line() {
  local turns tools out inp cw cr cost res
  turns=$(grep -c '"type":"assistant"' "$f" 2>/dev/null || echo 0)
  tools=$(grep -c '"type":"tool_use"' "$f" 2>/dev/null || echo 0)
  out=$(grep -o '"output_tokens":[0-9]*' "$f" | awk -F: '{s+=$2} END{print s+0}')
  inp=$(grep -o '"input_tokens":[0-9]*' "$f" | awk -F: '{s+=$2} END{print s+0}')
  cw=$(grep -o '"cache_creation_input_tokens":[0-9]*' "$f" | awk -F: '{s+=$2} END{print s+0}')
  cr=$(grep -o '"cache_read_input_tokens":[0-9]*' "$f" | awk -F: '{s+=$2} END{print s+0}')
  cost=$(awk "BEGIN{printf \"%.2f\", ($inp*15+$cw*18.75+$cr*1.5+$out*75)/1000000}")
  res=$(grep -rl "$sid" "$OUT"/*/result.txt 2>/dev/null | head -1)
  if [ -n "$res" ]; then
    printf '──[ turns:%s tools:%s · rounds:%s cost:$%s result:%s ]──' \
      "$turns" "$tools" "$(ls "$(dirname "$res")"/turn*.json 2>/dev/null | wc -l)" \
      "$(sed -n 's/^cost_usd: //p' "$res")" "$(sed -n 's/^result: //p' "$res")"
  else
    printf '──[ turns:%s tools:%s out-tok:%s · ~cost:$%s (est) ]──' "$turns" "$tools" "$out" "$cost"
  fi
}

echo "== monitoring $sid · live stream + stats (prints only when it CHANGES) · Ctrl-C to stop =="
# print the stats line ONLY when a value changes (no identical-line spam), acting as a progress marker
( last=""; while true; do line="$(stats_line)"; [ "$line" != "$last" ] && { printf '%s\n' "$line"; last="$line"; }; sleep 8; done ) &
tail -n +1 -f "$f" | render &                          # live stream of the transcript
wait                                                   # a signal fires the trap → cleanup reaps both
