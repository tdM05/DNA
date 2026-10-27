# Prop20 (Euclid I.20, triangle inequality) — proving notes

Main constructs: d' = extend_point_longer AB b a (c─a) [between b a d', |a-d'|>|c-a|];
d = proposition_3 a d' a c AB AC [between a d d', |a-d|=|a-c|]; DC = line_from_points d c.

## Step plan
- step1 (between b a d): from between b a d' + between a d d' + AB membership. DONE.
- step2 (|a-d|=|c-a|): from |a-d|=|a-c| + dist symm. DONE.
- step3 (distinctPointsOnLine d c DC): d,c on DC; d≠c since d on AB, c off AB. IN PROGRESS.
- step4 (∠a:d:c = ∠a:c:d): isosceles ADC (|a-d|=|a-c|), cite Prop 1.5.
    Apply proposition_5 a d c d' e AB DC AC with between a d d' (have) + between a c e (construct e=extend_point AC a c).
    conclusion first conjunct ∠a:d:c=∠a:c:d.
- step5 (∠b:c:d > ∠a:d:c): whole>part: ∠b:c:d > ∠a:c:d = ∠a:d:c (step4). a interior to ∠bcd via between b a d.
- step6 (|d-b|>|b-c|): cite Prop 1.19. proposition_19 b c d BC DC AB:
    formTriangle b c d BC DC AB + ∠b:c:d > ∠c:d:b → |b-d|>|b-c|. (∠c:d:b=∠b:d:c; use step6_assumption1.)
- step7 (|d-a|=|a-c|): restate (= step4_assumption1 type).
- step8 (|b-a|+|a-c|>|b-c|): from between b a d (|d-b|=|d-a|+|a-b|) + |d-a|=|a-c| (step7) + step6.
- step9 (|a-b|+|b-c|>|a-c|): "similarly", NO Main construction. Use generic helper `triineq`.
- step10 (|b-c|+|c-a|>|a-b|): "similarly", use generic helper `triineq`.

## Generic helper `triineq` (shared by step9, step10)
theorem helper_1_20_triineq (a b c)(AB BC AC)(h: formTriangle a b c AB BC AC)
    : |(b─a)| + |(a─c)| > |(b─c)|     -- apex a, bounds bc
Container: re-does extend/cut/isosceles(1.5)/1.19 generically.
- step9 call: triineq b a c AB AC BC  -> |a-b|+|b-c|>|a-c|.   @args: b a c AB AC BC
- step10 call: triineq c b a BC AB AC -> |b-c|+|c-a|>|a-b|.   @args: c b a BC AB AC
  (formTriangle c b a : line cb=BC, ba=AB, ac=AC)
No citation bracket in step9/step10 text -> no criterion-3 requirement there.
