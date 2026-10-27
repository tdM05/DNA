#!/usr/bin/env bash
# ============================================================================
# 5_test_step_order_hook.sh — does the PreToolUse step-order hook actually BLOCK
# writing a step past the frontier?
#
# WHY THIS EXISTS: the hook fails OPEN. If `.lake/faithful-certified/<prop>.json`
# is missing, find_frontier() returns None and EVERY write is allowed — silently.
# That happened once: the manifests were cleared out of a worktree's .lake, the
# hook went dead, and an arm ran a full prop with NO order enforcement. Nothing
# in the run log said so. This script catches that before a run, not after.
#
# NON-DESTRUCTIVE: only feeds JSON to the hook on stdin. Writes nothing, builds
# nothing, and does not touch the prop folder.
#
# Usage:  bash 5_test_step_order_hook.sh [worktree] [Book<N>/Prop<NN>]
#   defaults: worktree=od_only  prop=Book1/Prop20
#   exit 0 = enforcement live · exit 1 = hook is dead or mis-ordering
# ============================================================================
set -uo pipefail

ROOT="/h/56/taddmao/code/autoform/methodology_compare_worktrees"
WT="${1:-od_only}"
PROP="${2:-Book1/Prop20}"
REPO="$ROOT/$WT"
LEP="$REPO/LeanEuclidPlus"
HOOK="$REPO/.claude/hooks/step_order_hook.py"

[ -f "$HOOK" ]                  || { echo "FAIL: no hook at $HOOK"; exit 1; }
[ -f "$LEP/$PROP/Main.lean" ]   || { echo "FAIL: no $PROP/Main.lean in $WT"; exit 1; }

set +u; source "$HOME/.venvs/leaneuclid/bin/activate" 2>/dev/null; set -u
export CLAUDE_PROJECT_DIR="$REPO"

echo "=== step-order hook · worktree=$WT · prop=$PROP ==="

# ---- 1. what does the hook think the frontier is? --------------------------
read -r FRONTIER STATE NODES <<<"$(cd "$REPO" && python3 - "$HOOK" "$LEP/$PROP" <<'PY'
import sys, importlib.util, os
hook, propdir = sys.argv[1], sys.argv[2]
lep = os.path.dirname(os.path.dirname(propdir))        # .../LeanEuclidPlus
sys.path.insert(0, os.path.join(lep, "scripts"))
spec = importlib.util.spec_from_file_location("soh", hook)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
try:
    fr, names, state = m.find_frontier(propdir)
except Exception as e:
    print("ERROR ERROR 0"); sys.exit(0)
print(f"{fr} {state} {','.join(names) if names else '-'}")
PY
)"

echo "  frontier = $FRONTIER   state = $STATE"
echo "  nodes    = $NODES"

MANIFESTS=$(ls "$LEP/.lake/faithful-certified" 2>/dev/null | wc -l)
echo "  .lake/faithful-certified manifests = $MANIFESTS"

if [ "$FRONTIER" = "None" ] || [ "$FRONTIER" = "ERROR" ]; then
  echo
  echo "FAIL: frontier is '$FRONTIER' -> the hook ALLOWS EVERY WRITE (fails open)."
  [ "$MANIFESTS" -eq 0 ] && echo "      Cause: .lake/faithful-certified/ is empty or missing."
  echo "      Fix:  restore the manifests (e.g. cp -a ../full/LeanEuclidPlus/.lake/faithful-certified \\"
  echo "                                        $LEP/.lake/)"
  echo "      A stale manifest is FINE — staleness is hash-based, so every node reads as"
  echo "      'stale' after a GATE-3 reset and the frontier correctly lands on the first node."
  exit 1
fi

# ---- 2. the frontier node must be WRITABLE; a later node must be DENIED ----
ask() {  # $1 = node name -> prints "allow" or "deny"
  local out
  out=$(printf '{"tool_name":"Write","tool_input":{"file_path":"%s/%s/%s.lean","content":"x"}}' \
        "$LEP" "$PROP" "$1" | python3 "$HOOK" 2>/dev/null)
  case "$out" in (*'"permissionDecision": "deny"'*|*'"permissionDecision":"deny"'*) echo deny ;; (*) echo allow ;; esac
}

# pick a node strictly AFTER the frontier
LATER=$(python3 - "$FRONTIER" "$NODES" <<'PY'
import sys
fr, nodes = sys.argv[1], sys.argv[2].split(",")
i = nodes.index(fr) if fr in nodes else -1
print(nodes[i+1] if 0 <= i < len(nodes) - 1 else "")
PY
)

rc=0
got=$(ask "$FRONTIER")
printf '  write %-10s (the frontier)      -> %-5s  expect allow   %s\n' \
  "$FRONTIER" "$got" "$([ "$got" = allow ] && echo OK || { echo MISMATCH; rc=1; })"

if [ -z "$LATER" ]; then
  echo "  (frontier is the last node — no later node to test the deny path with)"
else
  got=$(ask "$LATER")
  printf '  write %-10s (past frontier)    -> %-5s  expect deny    %s\n' \
    "$LATER" "$got" "$([ "$got" = deny ] && echo OK || { echo MISMATCH; rc=1; })"
fi

echo
[ "$rc" -eq 0 ] && echo "PASS — step-order enforcement is LIVE." \
                || echo "FAIL — the hook is not enforcing order as expected."
exit "$rc"
