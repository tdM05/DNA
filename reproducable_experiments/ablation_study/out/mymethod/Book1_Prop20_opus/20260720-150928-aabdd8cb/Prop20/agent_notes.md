# Prop20 (triangle inequality) — proving notes

## STATUS: DONE — all 10 steps certified, --all PASS, wired (wire_main), zero sorry in Prop20.
## KEY LESSON: euclid_finish is FAST for a fact when betweenness hyps are in a SMALL context, but
## BLOWS UP (>45s) when betweenness sits in a LARGE hypothesis set (solver case-splits explode).
## Fix pattern (used for step6_form & step9_triineq_side_form): pull each distinctness/off-line
## conjunct into its OWN minimal-hyp leaf (no betweenness, or betweenness in tiny ctx), then the
## container's final formTriangle-assembly euclid_finish is a fast CHECK (all pieces present).
## step9/step10 ("similarly") share ONE generic lemma helper_1_20_step9_triineq (apex-p triangle
## inequality), reused via @args at both sites. Shared helper MUST carry a stepN_ prefix (step9_)
## or the step_order_hook denies the file (it maps files to Main nodes by prefix).


Figure: triangle ABC; extend BA beyond A to D (D above A), with AD = CA. Join DC. Order on line AB: B, A, D, D'.
Constructions in Main: d' = extend_point_longer AB b a (c-a); d = proposition_3 a d' a c AB AC (between a d d', |a-d|=|a-c|).

## Node plan (in order)
- step1: between b a d — from between b a d' + between a d d'. Leaf euclid_finish.
- step2: |a-d| = |c-a| — from |a-d|=|a-c| symmetry. Leaf.
- step3: distinctPointsOnLine d c DC — line_from_points d c; need d≠c. Leaf.
- step4 (cite Prop.1.5): ∠ a:d:c = ∠ a:c:d. Apply proposition_5 on triangle A-D-C (apex A, base D,C).
    proposition_5 needs between a b_arg d_arg AND between a c_arg e_arg (extension pts beyond both base vertices).
    beyond D: use d' (between a d d'). beyond C: construct e via extend_point AC a c.
    map: proposition_5 a d c d' e AB DC AC ; first conjunct ∠ a:d:c = ∠ a:c:d.  Container (constructs e).
- step5: ∠ b:c:d > ∠ a:d:c. angle addition: ray CA interior to angle BCD (a on seg bd) so ∠bcd = ∠bca+∠acd > ∠acd = ∠adc(step4).
- step6 (cite Prop.1.19): |d-b| > |b-c|. proposition_19 b c d BC DC AB with ∠b:c:d > ∠c:d:b (=∠b:d:c, step6_assumption1).
- step7: |d-a| = |a-c|. Leaf trivial.
- step8: |b-a|+|a-c| > |b-c|. from step6 (|d-b|>|b-c|), step7 (|d-a|=|a-c|), between b a d (|b-d|=|b-a|+|a-d|). Leaf linarith/euclid_finish.
- step9: |a-b|+|b-c| > |a-c|  ("similarly"). via generic tri_ineq lemma, apex b.
- step10: |b-c|+|c-a| > |a-b| ("similarly"). via generic tri_ineq lemma, apex c.

## Shared generic lemma: triineq.lean
theorem helper_1_20_triineq (p q r)(PQ QR PR)(htri: formTriangle p q r PQ QR PR) : |(q─p)| + |(p─r)| > |(q─r)|
  = "two sides meeting at apex p (pq, pr) sum > opposite qr". Replicates Euclid's construction generically.
Reused as have-node `triineq` in step9 (@args b a c AB AC BC) and step10 (@args c b a BC AB AC).
  step9 needs formTriangle b a c AB AC BC in ctx -> derive via euclid_finish as htri2 in step9.lean.
  step10 needs formTriangle c b a BC AB AC -> derive similarly.
  check: triineq(b,a,c): |q-p|+|p-r| = |a-b|+|b-c| > |a-c| ✓ (step9)
         triineq(c,b,a): |b-c|+|c-a| > |b-a|=|a-b| ✓ (step10) — note |b-a| vs |a-b| symmetry, may need rw.

## Key sigs
proposition_5 (a b c d e)(AB BC AC): formTriangle a b c AB BC AC ∧ |a-b|=|a-c| ∧ between a b d ∧ between a c e → ∠a:b:c=∠a:c:b ∧ ∠c:b:d=∠b:c:e
proposition_19 (a b c)(AB BC AC): formTriangle a b c AB BC AC ∧ ∠a:b:c>∠b:c:a → |a-c|>|a-b|
proposition_3 (a b c0 c1)(AB C): distinctOnLine a b AB ∧ distinctOnLine c0 c1 C ∧ |a-b|>|c0-c1| → ∃e, between a e b ∧ |a-e|=|c0-c1|
extend_point (L b c): distinctPointsOnLine b c L → ∃a, a.onLine L ∧ between b c a
formTriangle a b c AB BC CA := distinctOnLine a b AB ∧ b∈BC ∧ c∈BC ∧ c∈CA ∧ a∈CA ∧ AB≠BC ∧ BC≠CA ∧ CA≠AB
