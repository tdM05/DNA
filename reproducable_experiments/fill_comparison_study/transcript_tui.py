#!/usr/bin/env python3
"""transcript_tui.py — navigate a Claude Code .jsonl transcript.

Two things this tool surfaces:

  1. GIVE-UP / GOAL-FORCED-CONTINUE events.
     A `/goal` Stop hook was active ("...faithful, compiles with no sorry, ready for review").
     Every time the agent tried to STOP, the hook fired and (unless the condition held) forced it
     to keep going. Each attempt is recorded as a `stop_hook_summary` system entry. For each we show:
       - the agent's message right BEFORE it  = what it said as it tried to give up / declare done
       - the goal condition the hook enforced
       - the agent's message right AFTER it   = how it resumed
       - whether it was FORCED to continue (more work followed) or was the TERMINAL stop (goal met).

  2. TOOL WALL TIME.
     Every tool_use is matched to its tool_result by id; duration = result.ts - use.ts.
     Sortable chronologically or slowest-first.

Usage:
    python3 transcript_tui.py <transcript.jsonl>       # interactive TUI (curses)
    python3 transcript_tui.py <transcript.jsonl> --dump # plain-text report, no curses

TUI keys:
    TAB / 1 / 2      switch EVENTS <-> TOOLS tab
    j / k  or  down/up   move selection
    PgDn / PgUp      page
    g / G            top / bottom
    n / N            jump to next / prev give-up event (works in both tabs)
    s                (TOOLS) toggle sort: chronological <-> slowest-first
    ENTER            open full scrollable detail for the selected row
    q                quit  (ESC closes a detail view)
"""
import sys, os, json, datetime


def parse_ts(o):
    t = o.get("timestamp")
    if not t:
        return None
    try:
        return datetime.datetime.fromisoformat(t.replace("Z", "+00:00"))
    except ValueError:
        return None


def assistant_text(o):
    msg = o.get("message") or {}
    cont = msg.get("content")
    if not isinstance(cont, list):
        return ""
    out = [b.get("text", "") for b in cont if isinstance(b, dict) and b.get("type") == "text"]
    return "\n".join(t for t in out if t).strip()


def tool_input_summary(name, inp):
    if not isinstance(inp, dict):
        return ""
    if name == "Bash":
        cmd = (inp.get("command") or "").strip().splitlines()
        first = cmd[0] if cmd else ""
        desc = inp.get("description") or ""
        return (desc + " :: " + first).strip(" :") if desc else first
    if name in ("Write", "Edit", "Read", "NotebookEdit"):
        return inp.get("file_path") or inp.get("notebook_path") or ""
    if name in ("TaskCreate", "TaskUpdate"):
        return str(inp.get("description") or inp.get("prompt") or inp.get("status") or "")[:120]
    s = json.dumps(inp, ensure_ascii=False)
    return s[:160]


def load(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(l) for l in f if l.strip()]

    # --- tool calls: match tool_use -> tool_result by id ---
    uses = {}   # id -> dict(name, t0, input, idx)
    results = {}  # id -> t1
    for idx, o in enumerate(lines):
        msg = o.get("message") or {}
        cont = msg.get("content")
        if not isinstance(cont, list):
            continue
        for b in cont:
            if not isinstance(b, dict):
                continue
            if b.get("type") == "tool_use":
                uses[b["id"]] = dict(name=b.get("name", "?"), t0=parse_ts(o),
                                     input=b.get("input"), idx=idx)
            elif b.get("type") == "tool_result":
                results[b.get("tool_use_id")] = parse_ts(o)

    t0_all = min((u["t0"] for u in uses.values() if u["t0"]), default=None)
    tools = []
    for tid, u in uses.items():
        t1 = results.get(tid)
        dur = (t1 - u["t0"]).total_seconds() if (u["t0"] and t1) else None
        offset = (u["t0"] - t0_all).total_seconds() if (u["t0"] and t0_all) else None
        tools.append(dict(idx=u["idx"], name=u["name"], dur=dur, offset=offset,
                          summary=tool_input_summary(u["name"], u["input"]),
                          full=json.dumps(u["input"], ensure_ascii=False, indent=2),
                          t0=u["t0"]))
    tools.sort(key=lambda t: t["idx"])

    # --- give-up / goal-forced events: stop_hook_summary system entries ---
    summ_idx = [i for i, o in enumerate(lines)
                if o.get("type") == "system" and o.get("subtype") == "stop_hook_summary"]
    events = []
    for n, i in enumerate(summ_idx):
        o = lines[i]
        # preceding assistant text = the give-up / done declaration
        give_up = ""
        for j in range(i - 1, -1, -1):
            if lines[j].get("type") == "assistant":
                txt = assistant_text(lines[j])
                if txt:
                    give_up = txt
                    break
        # following assistant text = the resumption
        stop_at = summ_idx[n + 1] if n + 1 < len(summ_idx) else len(lines)
        resume = ""
        follow_assts = 0
        for j in range(i + 1, stop_at):
            if lines[j].get("type") == "assistant":
                txt = assistant_text(lines[j])
                if txt:
                    follow_assts += 1
                    if not resume:
                        resume = txt
        goal = ""
        for hi in (o.get("hookInfos") or []):
            goal = hi.get("promptText") or hi.get("command") or goal
        terminal = (n == len(summ_idx) - 1) and follow_assts == 0
        events.append(dict(idx=i, n=n + 1, ts=parse_ts(o), goal=goal,
                           give_up=give_up, resume=resume,
                           forced=not terminal, follow=follow_assts,
                           prevented=o.get("preventedContinuation")))
    return lines, tools, events, t0_all


# ---------------------------------------------------------------- plain dump
def fmt_dur(d):
    if d is None:
        return "   n/a"
    return "%6.1fs" % d


def dump(path):
    lines, tools, events, t0 = load(path)
    print("=" * 78)
    print("TRANSCRIPT:", path)
    print("lines=%d  tool_calls=%d  give_up_events=%d" % (len(lines), len(tools), len(events)))
    total = sum(t["dur"] for t in tools if t["dur"])
    print("total tool wall time: %.1f s (%.1f min)" % (total, total / 60))
    print()
    print("### GIVE-UP / GOAL-FORCED-CONTINUE EVENTS")
    for e in events:
        tag = "FORCED->continue" if e["forced"] else "TERMINAL (goal met)"
        print("-" * 78)
        print("[#%d] line %d  %s  %s" % (e["n"], e["idx"],
              e["ts"].strftime("%H:%M:%S") if e["ts"] else "?", tag))
        print("  goal: %s" % e["goal"])
        print("  gave up (before):")
        for ln in e["give_up"].splitlines()[:8]:
            print("    | " + ln)
        if e["resume"]:
            print("  resumed (after):")
            for ln in e["resume"].splitlines()[:4]:
                print("    > " + ln)
    print()
    print("### SLOWEST 15 TOOL CALLS")
    for t in sorted(tools, key=lambda x: -(x["dur"] or -1))[:15]:
        print("  %s  %-11s  %s" % (fmt_dur(t["dur"]), t["name"], t["summary"][:80]))
    from collections import Counter
    by = Counter()
    tt = Counter()
    for t in tools:
        by[t["name"]] += 1
        tt[t["name"]] += t["dur"] or 0
    print()
    print("### TOOL TOTALS")
    for name, c in by.most_common():
        print("  %-11s count=%-4d total=%7.1fs" % (name, c, tt[name]))


# ---------------------------------------------------------------- curses TUI
def run_tui(path):
    import curses
    import textwrap
    lines, tools, events, t0 = load(path)

    state = dict(tab=0, sort_dur=False)   # scalars only (kept mutable for closures)
    sel = [0, 0]   # per-tab selection index: [events, tools]
    top = [0, 0]   # per-tab scroll offset
    # tab 0 = EVENTS, tab 1 = TOOLS

    def sorted_tools():
        if state["sort_dur"]:
            return sorted(tools, key=lambda x: -(x["dur"] if x["dur"] is not None else -1))
        return tools

    def detail_lines_event(e):
        L = []
        L.append(("h", "GIVE-UP EVENT #%d   (line %d)" % (e["n"], e["idx"])))
        L.append(("", "time: %s   status: %s   follow-up assistant turns: %d" % (
            e["ts"].strftime("%Y-%m-%d %H:%M:%S") if e["ts"] else "?",
            "FORCED to continue" if e["forced"] else "TERMINAL (goal met)", e["follow"])))
        L.append(("", ""))
        L.append(("h", "GOAL ENFORCED BY HOOK"))
        for ln in textwrap.wrap(e["goal"], 92) or [""]:
            L.append(("", "  " + ln))
        L.append(("", ""))
        L.append(("h", ">>> WHAT THE AGENT SAID AS IT TRIED TO STOP (the 'give up')"))
        for para in e["give_up"].splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append(("g", "  " + ln))
        L.append(("", ""))
        L.append(("h", ">>> HOW IT RESUMED AFTER THE HOOK FORCED IT"))
        for para in (e["resume"] or "(no follow-up text)").splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append(("r", "  " + ln))
        return L

    def detail_lines_tool(t):
        L = []
        L.append(("h", "TOOL CALL  %s   (line %d)" % (t["name"], t["idx"])))
        L.append(("", "duration: %s    offset from start: %s" % (
            fmt_dur(t["dur"]),
            "%.1fs" % t["offset"] if t["offset"] is not None else "?")))
        L.append(("", "started: %s" % (t["t0"].strftime("%H:%M:%S") if t["t0"] else "?")))
        L.append(("", ""))
        L.append(("h", "INPUT"))
        for para in t["full"].splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append(("", "  " + ln))
        return L

    def draw_list(scr, h, w):
        tab = state["tab"]
        scr.addstr(0, 0, (" TRANSCRIPT TUI  " + os.path.basename(path))[:w - 1], curses.A_REVERSE)
        total = sum(x["dur"] for x in tools if x["dur"])
        tabs = "[1] EVENTS(%d)   [2] TOOLS(%d)" % (len(events), len(tools))
        meta = "tools wall %.0fs / %.1fmin" % (total, total / 60)
        scr.addstr(1, 0, tabs[:w - 1], curses.A_BOLD)
        scr.addstr(1, max(0, w - len(meta) - 1), meta[:w - 1])
        if tab == 0:
            hint = " j/k move  n/N next/prev  ENTER detail  TAB tools  q quit"
        else:
            sort = "slowest" if state["sort_dur"] else "chrono"
            hint = " j/k move  s sort(%s)  n/N give-up  ENTER detail  TAB events  q quit" % sort
        scr.addstr(2, 0, hint[:w - 1], curses.A_DIM)

        listtop = 4
        rows = h - listtop
        cursel = sel[tab]
        curtop = top[tab]
        if cursel < curtop:
            curtop = cursel
        if cursel >= curtop + rows:
            curtop = cursel - rows + 1
        top[tab] = curtop

        if tab == 0:
            items = events
            for r in range(rows):
                idx = curtop + r
                if idx >= len(items):
                    break
                e = items[idx]
                tag = "FORCED  " if e["forced"] else "TERMINAL"
                snip = (e["give_up"].splitlines() or [""])[0]
                line = "#%-2d %s %s  %s" % (e["n"],
                        e["ts"].strftime("%H:%M:%S") if e["ts"] else "  ?  ", tag, snip)
                attr = curses.A_REVERSE if idx == cursel else (
                    curses.color_pair(2) if e["forced"] else curses.color_pair(3))
                scr.addstr(listtop + r, 0, line[:w - 1], attr)
        else:
            items = sorted_tools()
            for r in range(rows):
                idx = curtop + r
                if idx >= len(items):
                    break
                t = items[idx]
                bar = ""
                if t["dur"] is not None:
                    bar = "#" * min(20, int(t["dur"] / 6))
                line = "%s %-11s %-20s %s" % (fmt_dur(t["dur"]), t["name"], bar, t["summary"])
                attr = curses.A_REVERSE if idx == cursel else (
                    curses.color_pair(4) if (t["dur"] or 0) >= 60 else curses.A_NORMAL)
                scr.addstr(listtop + r, 0, line[:w - 1], attr)

    def draw_detail(scr, h, w, dlines, off):
        for r in range(h):
            idx = off + r
            if idx >= len(dlines):
                break
            kind, txt = dlines[idx]
            attr = curses.A_NORMAL
            if kind == "h":
                attr = curses.A_BOLD | curses.color_pair(1)
            elif kind == "g":
                attr = curses.color_pair(3)
            elif kind == "r":
                attr = curses.color_pair(2)
            scr.addstr(r, 0, txt[:w - 1], attr)
        foot = " [j/k scroll  g/G ends  q/ESC back]  line %d-%d/%d" % (
            off + 1, min(off + h, len(dlines)), len(dlines))
        scr.addstr(h, 0, foot[:w - 1], curses.A_REVERSE)

    def main(scr):
        curses.curs_set(0)
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_CYAN, -1)
        curses.init_pair(2, curses.COLOR_YELLOW, -1)
        curses.init_pair(3, curses.COLOR_GREEN, -1)
        curses.init_pair(4, curses.COLOR_RED, -1)
        while True:
            scr.erase()
            h, w = scr.getmaxyx()
            draw_list(scr, h, w)
            scr.refresh()
            c = scr.getch()
            tab = state["tab"]
            n_items = len(events) if tab == 0 else len(tools)
            if c in (ord("q"),):
                return
            elif c in (ord("\t"), ord("1"), ord("2")):
                state["tab"] = 1 - tab if c == ord("\t") else (0 if c == ord("1") else 1)
            elif c in (ord("j"), curses.KEY_DOWN):
                sel[tab] = min(n_items - 1, sel[tab] + 1)
            elif c in (ord("k"), curses.KEY_UP):
                sel[tab] = max(0, sel[tab] - 1)
            elif c == curses.KEY_NPAGE:
                sel[tab] = min(n_items - 1, sel[tab] + (h - 5))
            elif c == curses.KEY_PPAGE:
                sel[tab] = max(0, sel[tab] - (h - 5))
            elif c == ord("g"):
                sel[tab] = 0
            elif c == ord("G"):
                sel[tab] = n_items - 1
            elif c == ord("s") and tab == 1:
                state["sort_dur"] = not state["sort_dur"]
                sel[1] = 0
                top[1] = 0
            elif c in (ord("n"), ord("N")):
                # jump between give-up events (in either tab)
                if tab == 0:
                    d = 1 if c == ord("n") else -1
                    sel[0] = max(0, min(len(events) - 1, sel[0] + d))
                else:
                    # move tool selection to the tool nearest the next/prev give-up event line
                    cur = sorted_tools()[sel[1]]["idx"] if tools else 0
                    ev_lines = [e["idx"] for e in events]
                    if c == ord("n"):
                        nxt = min([x for x in ev_lines if x > cur], default=None)
                    else:
                        nxt = max([x for x in ev_lines if x < cur], default=None)
                    if nxt is not None:
                        st = sorted_tools()
                        best = min(range(len(st)), key=lambda k: abs(st[k]["idx"] - nxt))
                        sel[1] = best
            elif c in (curses.KEY_ENTER, 10, 13):
                if tab == 0 and events:
                    dl = detail_lines_event(events[sel[0]])
                elif tab == 1 and tools:
                    dl = detail_lines_tool(sorted_tools()[sel[1]])
                else:
                    dl = []
                off = 0
                while True:
                    scr.erase()
                    h, w = scr.getmaxyx()
                    draw_detail(scr, h - 1, w, dl, off)
                    scr.refresh()
                    k = scr.getch()
                    if k in (ord("q"), 27):
                        break
                    elif k in (ord("j"), curses.KEY_DOWN):
                        off = min(max(0, len(dl) - 1), off + 1)
                    elif k in (ord("k"), curses.KEY_UP):
                        off = max(0, off - 1)
                    elif k == curses.KEY_NPAGE:
                        off = min(max(0, len(dl) - 1), off + (h - 2))
                    elif k == curses.KEY_PPAGE:
                        off = max(0, off - (h - 2))
                    elif k == ord("g"):
                        off = 0
                    elif k == ord("G"):
                        off = max(0, len(dl) - (h - 1))
    curses.wrapper(main)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    if not args:
        print(__doc__)
        sys.exit(2)
    p = args[0]
    if not os.path.exists(p):
        print("no such file:", p)
        sys.exit(2)
    if "--dump" in flags:
        dump(p)
    else:
        run_tui(p)
