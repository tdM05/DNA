#!/usr/bin/env python3
"""Supply check (criterion 1). Every `euclid_sentence` that carries `-- @assumption` tags must be
proven through a helper LEMMA whose signature BINDS each assumption type — so the assumption is an
EXPLICIT supplied hypothesis, not a fact implicitly consumed by a direct `euclid_finish`. Source-only
(no build); the wired `lake build` then confirms each supplied hypothesis actually discharges from
context. Steps WITHOUT @assumption tags are unaffected (they may be direct proofs).

Usage: python3 scripts/check_supply.py Book<B>/Prop<NN>[/Main.lean]
Exit 0 = OK · 1 = a tagged step is a direct proof, or an assumption isn't bound by its helper.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import faithful_lib as fl


def supply_problems(propdir):
    book = fl.book_num(propdir)
    src = open(fl.main_file(propdir), encoding="utf-8").read()
    problems = []
    for m in fl.SENTENCE_HEAD.finditer(src):
        sname = m.group(2)
        assumptions = fl._assumptions_above(src, m.start())
        if not assumptions:
            continue                                        # no tags → no requirement
        bf = fl.backing_file(propdir, sname)
        if bf is None:
            problems.append(f"{sname}: carries {len(assumptions)} @assumption(s) but is proved DIRECTLY "
                            f"(no backing lemma). A tagged step must be a helper lemma so each assumption "
                            f"is an explicit supplied hypothesis.")
            continue
        try:
            _objs, hyp_types = fl.parse_helper_objs(bf, book, sname)
        except fl.FaithfulError as e:
            problems.append(f"{sname}: cannot read helper signature ({e}).")
            continue
        binder = {fl._norm(t) for t in hyp_types}
        for _text, typ, _ov in assumptions:
            if fl._norm(typ) not in binder:
                problems.append(f"{sname}: @assumption `{typ}` is not a hypothesis of its helper — add it "
                                f"to the helper signature and supply it when wiring the step.")
    return problems


def main(arg):
    propdir = arg if os.path.isabs(arg) else os.path.join(fl.BOOK_ROOT, arg)
    if propdir.endswith("Main.lean"):
        propdir = os.path.dirname(propdir)
    problems = supply_problems(propdir)
    if problems:
        print("SUPPLY FAIL:")
        for p in problems:
            print("  -", p)
        return 1
    print("supply OK (every @assumption-tagged step is a helper lemma binding its assumptions)")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
