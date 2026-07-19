#!/usr/bin/env python3
"""Backing-file check (source-only, no build, instant).

Enforces the DECOMPOSITION faithfulness criterion that check_faithful's --relaxed mode drops —
applied IDENTICALLY to the ablated baseline and the full method:

  Every `euclid_sentence … (stepN : T)` in Main delegates to a lemma `helper_<book>_<prop>_stepN`
  that lives in its OWN file `stepN.lean` (Main imports it and its body references the helper). No
  inline proof survives this — Euclid's "since X, therefore Y" becomes a real lemma with X in context
  proving Y. (Further, recursive decomposition INSIDE a step is NOT required — only the top-level
  per-sentence backing file. Assumptions are NOT enforced here — how each helper's hypotheses are
  supplied is left to the prover.)

The full method produces this automatically (the wiring pipeline); the ablated arm must reproduce the
per-sentence lemma structure by hand.

Usage:  python3 scripts/check_backing.py Book<B>/Prop<NN>/Main.lean
Exit 0 = all pass · 1 = problems found · 2 = usage/parse error.
"""
import re, sys, os
import faithful_lib as fl


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
