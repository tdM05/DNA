#!/usr/bin/env python3
"""Per prop x method: count the times the LLM genuinely WANTED TO STOP -- i.e. it ended its
turn to address the human with a completion / a question / a give-up -- as opposed to the
harness `end_turn` pauses where it just parked itself waiting for a background job.

An assistant `stop_reason == "end_turn"` with user-facing text is classified:
  wait     -> "I'll wait for the monitor / background job ..."  (EXCLUDED: not a real stop)
  done     -> hands back: "ready for review", "grader PASS", "yours to run" ...
  asked    -> asks the human to decide: "Would you like ... or pause here?" (has '?')
  gave_up  -> "I cannot ...", "won't keep looping", "record as ablation fail-datum" ...
  other    -> substantive but uncategorized (reported, not counted as genuine)
genuine_stops = done + asked + gave_up.

For each genuine stop we also classify what made it CONTINUE, from the next human/injected prompt:
  goal   -> a "Stop hook" (goal-condition) re-prompt forced it onward
  human  -> a real human message
  ended  -> nothing followed: the session actually stopped there

Run bare:  python3 reproducable_experiments/fill_comparison_study/analyze_stops.py
Writes stops_detail.md (every counted stop's full text + trigger) and stops_summary.csv.
"""
import json
import re
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent
METHODS = {"naive": HERE / "naive_llm", "mine": HERE / "my_method"}

WAIT = re.compile(r"\b(wait|waiting|monitor event|notif|background job|stop polling|pause polling|"
                  r"resume (?:when|automatically)|re-invoke|be notified|completion (?:event|notification))\b", re.I)
GAVE_UP = re.compile(r"(cannot |can'?t (?:synth|prove|derive|close|do|locate|find|complete)|won'?t keep|"
                     r"unable to|not able to|fail-datum|ablation (?:data|fail)|the (?:exact )?blocker|"
                     r"reach limit|unprovable|give up|recommend recording|missing (?:step|construction))", re.I)
ASK = re.compile(r"(would you like|want me to|shall i|should i|or pause|or \(?[bc]\)?[\)\s]|choose|"
                 r"option \d|let me know|you (?:choose|decide)|or something else|prefer)", re.I)
DONE = re.compile(r"(ready for (?:your )?review|nothing further|yours to run|human'?s to run|grader pass|"
                  r"\bpass\.|compiles cleanly|ready to act|all set|ready for your|end to end.*(?:faithful|review))", re.I)


def classify(t):
    s = t.strip()
    if not s:
        return None                       # empty end_turn (thinking only) -> not a stop
    if GAVE_UP.search(s):
        return "gave_up"
    if ASK.search(s) and "?" in s:
        return "asked"
    if DONE.search(s):
        return "done"
    if WAIT.search(s):
        return "wait"
    return "other"


def atext(msg):
    c = msg.get("content")
    if isinstance(c, str):
        return c
    if isinstance(c, list):
        return " ".join(b.get("text", "") for b in c if isinstance(b, dict) and b.get("type") == "text")
    return ""


def user_prompt(obj):
    """Return the prompt string if this entry is a human/injected prompt, else None."""
    if obj.get("type") != "user":
        return None
    c = (obj.get("message") or {}).get("content")
    if isinstance(c, str):
        return c
    return None                           # list content = tool_result, not a prompt


def trigger_of(prompt):
    if prompt is None:
        return "ended"
    if "Stop hook" in prompt or "stop hook" in prompt:
        return "goal"
    if prompt.lstrip().startswith(("<task-notification", "<local-command", "<command-name")):
        return "system"                   # async/system, not a real continue decision
    return "human"


GEN = ("done", "asked", "gave_up")
rows, detail = [], []
for method, root in METHODS.items():
    for jsonl in sorted(root.glob("*/*.jsonl")):
        prop = jsonl.parent.name
        entries = []
        for line in jsonl.open(errors="replace"):
            try:
                entries.append(json.loads(line))
            except Exception:
                pass
        counts = dict(done=0, asked=0, gave_up=0, wait=0, other=0,
                      goal=0, human=0, ended=0, system=0)
        for i, obj in enumerate(entries):
            if obj.get("type") != "assistant":
                continue
            msg = obj.get("message") or {}
            if msg.get("stop_reason") != "end_turn":
                continue
            cat = classify(atext(msg))
            if cat is None:
                continue
            counts[cat] += 1
            if cat in GEN:
                trig = "ended"
                for nxt in entries[i + 1:]:
                    p = user_prompt(nxt)
                    if p is not None:
                        trig = trigger_of(p)
                        if trig == "system":
                            continue      # skip async/system, look for the real next prompt
                        break
                counts[trig] = counts.get(trig, 0) + 1
                detail.append((prop, method, cat, trig, atext(msg).strip()))
        counts["genuine"] = counts["done"] + counts["asked"] + counts["gave_up"]
        counts.update(prop=prop, method=method)
        rows.append(counts)

order = {"naive": 0, "mine": 1}
rows.sort(key=lambda r: (tuple(int(x) for x in r["prop"].split(".")), order[r["method"]]))

print("| prop | method | genuine stops | done | asked | gave_up | → by goal | → by human | → ended |")
print("|:----:|:------:|:-------------:|:----:|:-----:|:-------:|:--------:|:---------:|:-------:|")
for r in rows:
    print(f"| {r['prop']} | {r['method']} | {r['genuine']} | {r['done']} | {r['asked']} | {r['gave_up']} "
          f"| {r['goal']} | {r['human']} | {r['ended']} |")

for method in ("naive", "mine"):
    sub = [r for r in rows if r["method"] == method]
    g = sum(r["genuine"] for r in sub)
    print(f"\n**{method} totals** — genuine stops {g}  "
          f"(done {sum(r['done'] for r in sub)}, asked {sum(r['asked'] for r in sub)}, "
          f"gave_up {sum(r['gave_up'] for r in sub)}) | continued by goal {sum(r['goal'] for r in sub)}, "
          f"human {sum(r['human'] for r in sub)}, ended {sum(r['ended'] for r in sub)}")

# CSV
with open(HERE / "stops_summary.csv", "w", newline="") as fh:
    cols = ["prop", "method", "genuine", "done", "asked", "gave_up", "goal", "human", "ended", "wait", "other"]
    w = csv.DictWriter(fh, fieldnames=cols)
    w.writeheader()
    for r in rows:
        w.writerow({k: r.get(k, 0) for k in cols})

# detail markdown for human verification
with open(HERE / "stops_detail.md", "w") as fh:
    fh.write("# Genuine LLM 'want to stop' moments (excludes background-job wait pauses)\n\n")
    fh.write("Each entry: category + what made it continue, then the stop's text.\n")
    lastkey = None
    for prop, method, cat, trig, txt in detail:
        key = (prop, method)
        if key != lastkey:
            fh.write(f"\n## {method} / {prop}\n\n")
            lastkey = key
        fh.write(f"- **[{cat} → continued by {trig}]** {txt}\n\n")
print("\nwrote stops_summary.csv and stops_detail.md")
