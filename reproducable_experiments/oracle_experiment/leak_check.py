#!/usr/bin/env python3
"""Post-hoc leak check for LLM-oracle runs. Scans a run's transcript.jsonl for
evidence the WORKER reached outside its worktree (to crib the gold) or used git.
Any hit = AUTO-FAIL for that run, overriding a passing grade.

Lives in the MAIN checkout (not the worktree), so the worker never sees it and
cannot learn the patterns to game them.

  python3 leak_check.py <run_dir>          # check one run (dir with transcript.jsonl)
  python3 leak_check.py out                # scan ALL runs under out/
  python3 leak_check.py out --mark         # + write LEAK.txt and flip result.txt to FAIL

Exit code: 1 if any violation found, 0 if all clean, 2 if no transcripts found.

WHAT IT CHECKS (the actual leak surface — the gold lives in sibling checkouts):
  - git in any form (already blocked live; belt-and-suspenders).
  - any reference to another checkout of the project: `<sibling>/LeanEuclidPlus` for
    sibling in {DNA, DNA-main, full, od_only, ablated}, any `/autoform/DNA[-main]/`
    path, or the eval harness `reproducable_experiments/oracle_experiment`. Catches
    absolute AND relative references in the agent's commands / file opens / <<<RUN>>>.
  It scans the agent's ACTIONS (bash commands, tool file paths, RUN payloads), NOT its
  free reasoning text, to avoid false positives on paths it merely talks about.

LIMIT (document honestly): catches DIRECT references. It cannot catch obfuscation
(base64 a path, or `cp` gold to /tmp then read /tmp). True immunity needs an FS sandbox.
"""
import sys, os, json, re, glob

TOOL_KEYS = ("command", "file_path", "path", "notebook_path")
GIT  = re.compile(r'(?:^|[^A-Za-z0-9_])git(?:[^A-Za-z0-9_]|$)')
GOLD = re.compile(r'(?:DNA|DNA-main|full|od_only|ablated)/LeanEuclidPlus'
                  r'|/autoform/DNA(?:-main)?/'
                  r'|reproducable_experiments/oracle_experiment')

def collect(obj, actions, texts):
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in TOOL_KEYS and isinstance(v, str): actions.append(v)
            if k == "text" and isinstance(v, str):    texts.append(v)
            collect(v, actions, texts)
    elif isinstance(obj, list):
        for x in obj: collect(x, actions, texts)

def scan(tpath):
    actions, texts = [], []
    with open(tpath, encoding="utf-8", errors="replace") as f:
        for line in f:
            line = line.strip()
            if not line: continue
            try: collect(json.loads(line), actions, texts)
            except Exception: continue
    run_blocks = [m for t in texts for m in re.findall(r'<<<RUN.*?>>>(.*?)<<<END>>>', t, re.S)]
    hits = {"git": [], "outside": []}
    for cand in actions + run_blocks:
        for ln in cand.splitlines():
            if GIT.search(ln):  hits["git"].append(ln.strip())
            if GOLD.search(ln): hits["outside"].append(ln.strip())
    return hits

def main():
    pos  = [a for a in sys.argv[1:] if not a.startswith("--")]
    mark = "--mark" in sys.argv
    target = pos[0] if pos else os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
    # scans the worker transcript.jsonl AND the oracle_*.transcript.jsonl (both the worker and the
    # agent-oracle can reach outside the worktree, so both are checked).
    tpaths = sorted(glob.glob(os.path.join(target, "**", "*transcript.jsonl"), recursive=True))
    if not tpaths:
        print(f"no transcript.jsonl under {target}"); sys.exit(2)

    any_viol = False
    for tp in tpaths:
        rundir = os.path.dirname(tp)
        hits = scan(tp)
        viol = bool(hits["git"] or hits["outside"])
        rel = os.path.relpath(rundir, target) if os.path.isdir(target) else rundir
        print(f"[{'VIOLATION' if viol else 'clean'}] {rel}")
        if not viol: continue
        any_viol = True
        for kind in ("git", "outside"):
            for h in dict.fromkeys(hits[kind]):
                print(f"    {kind}: {h[:160]}")
        if mark:
            kinds = "+".join(k for k in ("git", "outside") if hits[k])
            with open(os.path.join(rundir, "LEAK.txt"), "w") as f:
                f.write("LEAK VIOLATION — AUTO-FAIL\n")
                for kind in ("git", "outside"):
                    for h in dict.fromkeys(hits[kind]): f.write(f"{kind}: {h}\n")
            rp = os.path.join(rundir, "result.txt")
            if os.path.exists(rp):
                s = open(rp).read()
                s = re.sub(r'(?m)^result: .*$',      'result: FAIL', s)
                s = re.sub(r'(?m)^fail_reason: .*$',  f'fail_reason: leak_{kinds}', s)
                open(rp, "w").write(s)
    print("\n" + ("ANY VIOLATION" if any_viol else "ALL CLEAN"))
    sys.exit(1 if any_viol else 0)

if __name__ == "__main__":
    main()
