#!/usr/bin/env python3
"""Seed a step-order manifest for props that have none, so the PreToolUse hook
enforces in-order step writes FROM THE FIRST WRITE instead of failing open.

THE PROBLEM
  `step_order_hook.py` reads `.lake/faithful-certified/<Book>_<Prop>.json` to
  learn which node is the frontier. If that file is absent it returns
  frontier=None and ALLOWS EVERY WRITE — silently, with nothing in the run log.
  A manifest only appears once `check_step.py` certifies a node, so a prop that
  has never been certified in this worktree runs unenforced until the agent's
  first certification.

THE FIX
  Write a seed manifest that marks step1 "certified" with DELIBERATELY WRONG
  file hashes. Staleness is hash-based, so the board reads step1 as *stale* —
  i.e. NOT done — and the frontier parks on step1. Net effect: full in-order
  enforcement from the very first write, and nothing is falsely claimed as done
  (stale == not done). This is the same state a real prop is in after a GATE-3
  reset, which is why it is safe.

  Writes only into `.lake/` (gitignored). Never touches a Book*/Prop* file.

Usage:
  python3 seed_step_order_manifests.py <worktree> [Book<N>/Prop<NN> ...]
  python3 seed_step_order_manifests.py od_only --experiment-props
  add --dry-run to print what would be written
"""
import json, os, sys

ROOT = "/h/56/taddmao/code/autoform/methodology_compare_worktrees"

# the 15 propositions of the RQ2 fill-stage ablation
EXPERIMENT_PROPS = [
    "Book1/Prop03", "Book1/Prop06", "Book1/Prop12", "Book1/Prop18", "Book1/Prop20",
    "Book1/Prop27", "Book1/Prop30", "Book1/Prop36", "Book1/Prop45",
    "Book2/Prop03", "Book2/Prop12",
    "Book3/Prop06", "Book3/Prop11", "Book3/Prop25", "Book3/Prop36",
]

STALE = "0" * 64   # never equals a real sha256 -> the node always reads as stale


def seed(lep, prop, dry=False):
    key = prop.replace("/", "_")
    mpath = os.path.join(lep, ".lake", "faithful-certified", f"{key}.json")
    main_rel = f"{prop}/Main.lean"

    if not os.path.isfile(os.path.join(lep, main_rel)):
        return "no Main.lean"
    if os.path.isfile(mpath):
        return "already has a manifest — left alone"
    if dry:
        return f"would write {mpath}"

    manifest = {
        "certified": {"step1": {"inputs": [main_rel, f"{prop}/step1.lean"], "kind": "leaf"}},
        "files": {main_rel: STALE, f"{prop}/step1.lean": STALE},
        "prop": prop,
        "updated": "seeded by seed_step_order_manifests.py (stale hashes -> frontier=step1)",
    }
    os.makedirs(os.path.dirname(mpath), exist_ok=True)
    with open(mpath, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)
    return "SEEDED"


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    dry = "--dry-run" in sys.argv
    if not args:
        print(__doc__)
        sys.exit(1)
    wt, rest = args[0], args[1:]
    props = EXPERIMENT_PROPS if ("--experiment-props" in sys.argv or not rest) else rest
    lep = os.path.join(ROOT, wt, "LeanEuclidPlus")
    if not os.path.isdir(lep):
        print(f"no such worktree: {lep}")
        sys.exit(1)

    print(f"worktree={wt}{'  (DRY RUN)' if dry else ''}")
    for p in props:
        print(f"  {p:<16} {seed(lep, p, dry)}")


if __name__ == "__main__":
    main()
