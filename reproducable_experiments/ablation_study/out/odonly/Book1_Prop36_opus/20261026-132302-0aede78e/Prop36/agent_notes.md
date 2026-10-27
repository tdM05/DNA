# Prop36 Phase B notes

Faithful Main follows branch 1 (`e.sameSide b CH`) of Book1Variants/Prop36.lean (`proposition_36'`).
Faithful signature adds `between a d h ∧ between a e h` (pins config, no by_cases needed).

Config (diagram 36.png):
- top line AH: a d e h (left→right)
- bottom line BG: b c f g
- parallelogram ABCD = formParallelogram a d b c AH BG AB CD (AB=left side a-b, CD=side c-d)
- parallelogram EFGH = formParallelogram e h f g AH BG EF HG (EF=side e-f, HG=side h-g)
- BE = line_from_points b e, CH = line_from_points c h

Steps: step1 join BE,CH; step2 |bc|=|eh|; step3 BG∥AH; step4 eb,hc join; step5 |eb|=|hc| & BE∥CH [1.33];
step6 formParallelogram e h b c AH BG BE CH [1.34]; step7 EBCH=ABCD [1.35]; step8 EFGH=EBCH; step9 concl.
step2_assumption2 (gap): |fg|=|eh| [Prop 1.34].

Cited props: 1.33 (proposition_33), 1.34 (proposition_34), 1.35 (proposition_35').
Original variant used proposition_34, proposition_33, proposition_35'.

## progress
- step1 CERTIFIED (full-context euclid_finish for b≠e,c≠h; trimmed ctx timed out → use full parallelogram atoms)
- step2_assumption2 CERTIFIED (proposition_34 on EFGH, build HF=line_from_points h f in-body)
- step2 CERTIFIED (rw transitivity)
- step3 CERTIFIED (intersection_symm)
- step4 CERTIFIED (full-context euclid_finish, mirror of step1)
- step5 CERTIFIED: container applies proposition_33 e h b c AH BG BE CH;
  sub-node step5_ss : e.sameSide b CH proved by euclid_finish w/ parallelogram atoms + between a d h/a e h.
  KEY: e.sameSide b CH IS derivable from the faithful between-hyps (the branch-1 condition the variant by_cases'd).
- step5_ss.lean is SHARED — reuse as `have step5_ss` in step6 (same objects a b c d e h / AH BG AB CD CH).
## CITATION ANALYSIS (criterion-3) — IMPORTANT, report to human
--dependency requires each sentence's cited [Prop.~B.N] appear in THAT sentence's own helper cone
(assumption-gap nodes like step2_assumption2 are SEPARATE roots, NOT in step2's cone).
- step2 (1.36.2) cites [1.34]: LEGIT (|FG|=|EH| is Prop 1.34 opposite-sides). FIX: step2.lean itself
  applies proposition_34 on EFGH (build HF in-body). (step2_assumption2 also applies 34 for the gap —
  unavoidable redundancy since gap is a separate root.)
- step7 (1.36.7) cites [1.35]: LEGIT (EBCH=ABCD same base BC, same parallels). FIX: apply proposition_35'.
- step6 (1.36.6) cites [1.34] for "EBCH is a parallelogram": EDITORIAL. formParallelogram follows from
  EB∥CH (Prop1.33/step5) + EH∥BC (AH∥BG); Prop 1.34 (props of a parallelogram) cannot FORM one.
  Heath has no citation here. → @suppress_deps_check.
- step8 (1.36.8) cites [1.34] for "EFGH equal to EBCH": EDITORIAL (should be 1.35). Same base EH / same
  parallels area-equality = Prop 1.35 ("for the same reasons" as step7). Heath cites I.35. Proven via
  proposition_35'. → @suppress_deps_check.
@suppress lines are full-line comments → stripped from content_sha → do NOT re-stale certified nodes.

## FINAL STATE (Phase B complete)
All 10 Main nodes ✓ certified; criterion-3 ✓ (step2→prop34, step7/step8→prop35', step6/step8 [1.34] waived
via @suppress_deps_check — editorial source citations, documented). integrity ✓, no orphans ✓.
--status says --all GUARANTEED to pass. step7/step8 builds are slow (~5min) — they pull Book1Variants.Prop35
+ its transitive deps (prop34'/29''''/4/35...). Next: run --all (witness), then wire_main.py (Phase C).
NOTE for human: two @suppress_deps_check added (step6, step8) for the source's editorial [Prop.~1.34]
brackets — please review grep -rn @suppress_deps_check Book1/Prop36.
