# Prop04 Phase B rebuild (backing files were deleted; recreating from euclid-figures recipes)

## Environment facts
- Book1 deps (proposition_29/5/6/34, etc.) are FAITHFUL WIP with `sorry` — these dep sorries are
  TOLERATED by check_step (line 540/756). Only MY OWN stepN.lean bodies must be sorry-free.
- `--provable` prints "P pending ... sorry at Book1/..." — that's FINE (dep sorry). "P ok" needs own-file clean.
- Timeouts are SMT (euclid_finish) cost, NOT dep-load. Keep ≤ a couple euclid_finish per file; use
  Helpers library lemmas as TERMS (zero SMT) for off-line/sameSide/line-ne.

## Off-line derivation pattern (euclid_finish CANNOT leap parallel→off-line; use library terms)
- `¬d.onLine AB` ← `offLine_of_right_angle a b d AB haAB hbAB hab had hang` (needs a≠d).
- `a≠d` ← `by euclid_finish` with `|a─d|=|a─b|` + `a≠b` in ctx (length positivity). PASS `|a─d|=|a─b|` as binder.
- `¬c.onLine AD` ← `offLine_of_two_points c a d AB AD hcAB haAB hca haAD hdAD hd_off_ab`.
- `¬c.onLine BD` ← `offLine_of_two_points c b d AB BD hcAB hbAB hcb hbBD hdBD hd_off_ab`.
- `¬d.onLine CF` ← `offLine_of_parallel d c AD CF hdAD hcCF hc_off_ad hpar`  (hpar = ¬CF.intersectsLine AD).
- `L≠M` ← `line_ne_of_offLine p L M hpL hpoffM` (term); flip with `.symm`.
- sameSide of two pts on a parallel: `sameSide_of_parallel_both p q L M hpL hqL hLneM hpar'` (hpar' = ¬(L.intersectsLine M)).
- opposite via between: `not_sameSide_of_between a b c L hbL hbet` (¬a.sameSide c L from between a b c, b on L).
- betweenness of crossing: `between_of_not_sameSide a b c L M hLM hbL hbM haM hcM hab hcb hac hns`.
- segment-endpoint sameSide: `sameSide_of_between a b c L haL hboffL hbet` ⟹ b.sameSide c L.

## DONE (certified via --drive): step1,2,3,4,5 (+ step5_bgd, step5_ss).
step5 = corresponding angle ∠c:g:b=∠a:d:b via `proposition_29'''' c a b g d CF AD BD` (container; subs
step5_bgd [between b g d, pasch_4 chain], step5_ss [c.sameSide a BD, pasch_2]).
IN-ORDER hook is strict: fill ONLY current frontier node, then `--drive`; can't edit ahead.
