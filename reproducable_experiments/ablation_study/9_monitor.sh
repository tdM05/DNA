#!/usr/bin/env bash
# Live-monitor a running experiment — pretty-prints each turn as it happens.
# READ-ONLY (tail -f on the transcript); it cannot interfere with the experiment.
# Run in a SECOND terminal, any time (before/during/after the run).
#
# Usage:
#   bash 9_monitor.sh                # auto: follows the newest transcript for this project
#   bash 9_monitor.sh <session-id>   # follow a specific session (e.g. from naive_prop01_session.txt)
set -uo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"
PROJ="$HOME/.claude/projects/${SLUG}"

pick() { ls -t "$PROJ"/*.jsonl 2>/dev/null | head -1; }

if [ -n "${1:-}" ]; then
  F="$PROJ/$1.jsonl"
else
  F="$(pick)"
fi

# wait for a transcript to exist (e.g. if you launch the monitor a beat early)
until [ -n "${F:-}" ] && [ -f "$F" ]; do
  echo "waiting for a transcript in $PROJ ..."; sleep 2
  F="$(pick)"
done

echo "== monitoring: $F"
echo "== read-only; Ctrl-C to stop. If this is the wrong session (e.g. your own chat),"
echo "== re-run with the session id:  bash 9_monitor.sh <session-id>"
echo
# whole run so far + follow live; --unbuffered so it prints each turn the instant it lands
tail -n +1 -f "$F" | jq -rc --unbuffered '
  if .type=="assistant" then
    (.message.content[]? |
       if .type=="text" then "\n💬 " + .text
       elif .type=="tool_use" then "🔧 " + .name + "  " + ((.input|tostring)[0:200])
       else empty end)
  elif .type=="user" then
    (.message.content[]? |
       if (type=="object" and .type=="tool_result")
       then "   ↳ " + ((.content|tostring)[0:240]) else empty end)
  else empty end' 2>/dev/null
