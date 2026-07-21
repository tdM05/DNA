#!/usr/bin/env python3
"""Backing-file check (source-only, no build, instant).

Enforces the DECOMPOSITION faithfulness criterion that check_faithful's --relaxed mode drops —
applied IDENTICALLY to the ablated baseline and the full method:

  (A) Every `euclid_sentence … (stepN : T)` delegates to a lemma `helper_<book>_<prop>_stepN` in its
      OWN file `stepN.lean` (Main imports it + its body references the helper) — no inline proof.
      (Recursive decomposition INSIDE a step is NOT required — only the top-level per-sentence file.)
  (B) Assumption consumption — so both arms read IDENTICALLY: every hypothesis proof uses
      `euclid_assumption` (never bare `(by assumption)`), each shows its type `(show TYPE; …)`, and
      each `-- @assumption ("TEXT", TYPE)` is consumed as `euclid_assumption "TEXT" (show TYPE; …)` so
      the cited NL text marks WHERE the fact is used.

The full method produces this automatically (the wiring pipeline); the ablated arm must reproduce the
per-sentence lemma structure by hand.

Usage:  python3 scripts/check_backing.py Book<B>/Prop<NN>/Main.lean
Exit 0 = all pass · 1 = problems found · 2 = usage/parse error.
"""
import re, sys, os
import faithful_lib as fl


def _norm(s):
    return " ".join(s.split())


def _helper_call(src, helper):
    """The balanced-paren `(helper_… args)` delegation call for `helper`, or None. Scoped to THIS
    helper's name, so a sentence's own call is isolated from surrounding frame code (wlog/reductio
    branches, which use OTHER helpers + bare `(by assumption)`)."""
    m = re.search(r'\b' + re.escape(helper) + r'\b', src)
    if not m:
        return None
    i = m.start() - 1
    while i >= 0 and src[i].isspace():                       # the '(' just before the helper name
        i -= 1
    if i < 0 or src[i] != '(':
        return None
    depth, j = 0, i
    while j < len(src):
        if src[j] == '(':
            depth += 1
        elif src[j] == ')':
            depth -= 1
            if depth == 0:
                return src[i:j + 1]
        j += 1
    return None


def _report(label, problems, n):
    if problems:
        print(f"  [FAIL] {label}")
        for p in problems:
            print(f"         - {p}")
        return 1
    print(f"  [PASS] {label}")
    print(f"         {n} checked")
    return 0


def check_backing(main_rel):
    main_path = os.path.realpath(main_rel)
    if not os.path.isfile(main_path):
        print(f"  [FAIL] no such file: {main_rel}")
        return 1
    propdir = os.path.dirname(main_path)
    propbase = os.path.basename(propdir)                 # e.g. "Prop01"
    book = fl.book_num(propdir)
    prop = fl.prop_num(propdir)
    src = open(main_path, encoding="utf-8").read()

    print(f"=== {os.path.join(propbase, 'Main.lean')} — MODE: backing (source, no build) ===")
    steps = list(fl.SENTENCE_HEAD.finditer(src))
    if not steps:
        print("  [FAIL] no euclid_sentence steps with a claim binder found")
        return 1

    # Every sentence is a lemma in its own file: stepN.lean exists, defines helper_<book>_<prop>_stepN,
    # Main imports it, and Main's body references the helper (so nothing is proven inline).
    problems = []
    for m in steps:
        sname = m.group(2)                               # e.g. "step4"
        helper = fl.helper_name(book, prop, sname)       # helper_<book>_<prop>_step4
        try:
            bf = fl.backing_file(propdir, sname)
        except fl.FaithfulError as e:
            problems.append(f"{sname}: {e}")
            continue
        if bf is None:
            problems.append(f"{sname}: no backing file '{sname}.lean' in {propbase}/ "
                            f"(every sentence must be a lemma in its own file)")
            continue
        bftext = open(bf, encoding="utf-8").read()
        if not re.search(r'\btheorem\s+' + re.escape(helper) + r'\b', bftext):
            problems.append(f"{sname}: {os.path.basename(bf)} does not define `theorem {helper}`")
        if not re.search(r'(?m)^\s*import\s+Book%d\.%s\.%s\b'
                         % (book, re.escape(propbase), re.escape(sname)), src):
            problems.append(f"{sname}: Main does not `import Book{book}.{propbase}.{sname}`")
        if not re.search(r'\b' + re.escape(helper) + r'\b', src):
            problems.append(f"{sname}: Main never references `{helper}` "
                            f"(the sentence must delegate to its helper, not prove inline)")
    rc = _report("every sentence delegates to helper_<book>_<prop>_stepN in its own file",
                 problems, len(steps))

    # ── (B) assumption consumption — SCOPED to each sentence's OWN helper call (never the wlog /
    # reductio FRAME around it, which legitimately uses bare `(by assumption)`):
    #   • every hypothesis proof-arg `(by …)` in the call is `euclid_assumption … (show TYPE; …)`
    #     — enforced by counting: #`(by …)` == #`show` == #`euclid_assumption`,
    #   • each `-- @assumption ("TEXT", TYPE)` is consumed as `euclid_assumption "TEXT" (show TYPE; …)`.
    b_problems = []
    for m in steps:
        sname = m.group(2)
        call = _helper_call(src, fl.helper_name(book, prop, sname))
        if call is None:
            continue                                         # part A already reports the missing helper
        a = len(re.findall(r'\(\s*by\b', call))              # hypothesis proof-args
        s = len(re.findall(r'\bshow\b', call))               # shows
        e = len(re.findall(r'\beuclid_assumption\b', call))  # euclid_assumptions
        if not (a == s == e):
            b_problems.append(f"{sname}: {a} hypothesis arg(s) `(by …)` but {e} euclid_assumption / {s} show "
                              f"— every hypothesis must be `(by euclid_assumption \"…\" (show TYPE; assumption))`")
        # per distinct @assumption TYPE: it must be consumed via euclid_assumption with ONE of its
        # (non-empty) NL texts + show. Duplicate @assumptions (same type, different phrasing from the
        # same sentence) are satisfied by any one of their texts — a redundant phrasing isn't required.
        by_type = {}
        for text, typ, *_ in (fl._assumptions_above(src, m.start()) or []):
            by_type.setdefault(_norm(typ), set()).add(text)
        for typ_n, texts in by_type.items():
            ok = False
            for t in texts:
                if not t:
                    continue
                h = re.search(r'euclid_assumption\s*"' + re.escape(t) + r'"\s*\(\s*show\s+(.+?)\s*;',
                              call, re.DOTALL)
                if h and _norm(h.group(1)) == typ_n:
                    ok = True
                    break
            if not ok:
                shown = " / ".join(sorted(repr(t) for t in texts))
                b_problems.append(f"{sname}: @assumption type `{typ_n}` (NL text {shown}) not consumed as "
                                  f"`euclid_assumption \"<its NL text>\" (show {typ_n}; assumption)`")
    rc |= _report("each sentence's helper call supplies every hypothesis via euclid_assumption (show type)",
                  b_problems, len(steps))

    print("  => " + ("ALL PASS" if rc == 0 else "PROBLEMS FOUND") + " (backing mode)")
    return rc


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("-")]
    if len(args) != 1:
        print("usage: python3 scripts/check_backing.py Book<B>/Prop<NN>/Main.lean")
        return 2
    return check_backing(args[0])


if __name__ == "__main__":
    sys.exit(main(sys.argv))
