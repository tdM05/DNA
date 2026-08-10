#!/usr/bin/env python3
"""Bootstrap PLACEHOLDER PropNN/Main.lean folders for a freshly-extracted book (4-13).

Unlike `scaffold_stub.py` (which copies a REAL `theorem proposition_N` signature out of a
flat Book-1 original), these books have NO Lean statement yet — writing the real signature is
the manual, human-reviewed `faithful-signature` phase (one prop at a time; see the skill). So
this only lays down the folder skeleton with a COMPILING placeholder whose goal is `True` and a
`TODO(faithful-signature)` marker pointing at the source text. The placeholder is meant to be
OVERWRITTEN by the faithful-signature step, which replaces it with the translated
`theorem proposition_N : … := by sorry`.

Prop count per book is read from the extracted `Book<N>/data/texts_proofs/*.txt` (so this must run
AFTER extract_book.py). **Skips** any PropNN whose Main.lean already exists (never clobbers real work);
`--force` overwrites placeholders.

Usage:
  python3 scripts/scaffold_placeholder_mains.py --book 4            # one book
  python3 scripts/scaffold_placeholder_mains.py --book 4 5 6        # several
  python3 scripts/scaffold_placeholder_mains.py --all              # books 4-13
  python3 scripts/scaffold_placeholder_mains.py --book 4 --dry-run
  python3 scripts/scaffold_placeholder_mains.py --book 4 --force
"""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import faithful_lib as L

ALL_BOOKS = list(range(4, 14))


def placeholder_text(book, n):
    return f"""import SystemE

namespace Elements.Book{book}

-- TODO(faithful-signature): translate Prop {n}'s enunciation into `theorem proposition_{n}`.
-- PLACEHOLDER only — source text: Book{book}/data/texts_proofs/{n}.txt
theorem proposition_{n} : True := by
  trivial

end Elements.Book{book}
"""


def prop_nums(book):
    tp = os.path.join(L.BOOK_ROOT, f"Book{book}", "data", "texts_proofs")
    if not os.path.isdir(tp):
        raise L.FaithfulError(
            f"no extracted texts at {tp} — run extract_book.py --book {book} first"
        )
    nums = sorted(
        int(m.group(1))
        for f in os.listdir(tp)
        for m in [re.fullmatch(r"(\d+)\.txt", f)]
        if m
    )
    if not nums:
        raise L.FaithfulError(f"no <n>.txt files in {tp}")
    return nums


def main():
    ap = argparse.ArgumentParser(description="Bootstrap placeholder PropNN/Main.lean folders.")
    ap.add_argument("--book", nargs="+", type=int, help="book number(s), e.g. 4 5")
    ap.add_argument("--all", action="store_true", help="books 4-13")
    ap.add_argument("--dry-run", action="store_true", help="report only; write nothing")
    ap.add_argument("--force", action="store_true", help="overwrite an existing Main.lean")
    args = ap.parse_args()

    books = ALL_BOOKS if args.all else (args.book or [])
    if not books:
        ap.error("give --book N [N ...] or --all")

    grand_created = grand_skipped = 0
    for book in books:
        try:
            nums = prop_nums(book)
        except L.FaithfulError as e:
            print(f"Book{book}: SKIP — {e}")
            continue
        created, skipped = [], []
        for n in nums:
            target_dir = os.path.join(L.BOOK_ROOT, f"Book{book}", f"Prop{n:02d}")
            target = os.path.join(target_dir, "Main.lean")
            if os.path.exists(target) and not args.force:
                skipped.append(n)
                continue
            if not args.dry_run:
                os.makedirs(target_dir, exist_ok=True)
                with open(target, "w", encoding="utf-8") as f:
                    f.write(placeholder_text(book, n))
            created.append(n)
        verb = "would create" if args.dry_run else "created"
        msg = f"Book{book}: {verb} {len(created)}"
        if skipped:
            msg += f", skipped {len(skipped)} existing"
        print(msg)
        grand_created += len(created)
        grand_skipped += len(skipped)

    verb = "would create" if args.dry_run else "created"
    print(f"TOTAL: {verb} {grand_created}, skipped {grand_skipped} existing")


if __name__ == "__main__":
    main()
