import SystemE
import Book3.Prop10.Main
import Book3.Prop24.step1
import Book3.Prop24.step2
import Book3.Prop24.step3
import Book3.Prop24.step4
import Book3.Prop24.step5
import Book3.Prop24.step6
import Book3.Prop24.step7
import Book3.Prop24.step8
import Book3.Prop24.step1_assumption1
import Book3.Prop24.step1_assumption2
import Book3.Prop24.hnot_inside
import Book3.Prop24.hnot_outside
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.24. "Similar segments of circles on equal straight-lines are equal to one another."
-- Faithful MAP (statement + sentence claims; bodies sorry). Uses the CircularSegment sort:
-- the goal is the LITERAL "segment AEB = segment CFD", i.e. ⌓ a:e:b = ⌓ c:f:d (equal AREAS),
-- NOT the old `AEB = CFD` circle-identity dodge, and the two chords AB, CD are genuinely
-- distinct (equal length), as Euclid states — not pre-collapsed onto one chord.
--
-- The proof is by SUPERPOSITION: apply segment AEB onto CFD (A→C, AB→CD). Since |AB|=|CD|, B lands
-- on D; the moved segment coincides with CFD (else the "miss" case gives two circles cutting at
-- >2 points, impossible by III.10 — see the @euclid_gap on step 4), hence (C.N.4) the areas equal.
--
-- Superposition is modelled with two DEFERRED maps: `ImgSegment : Point → Point` for the moved
-- points (like Prop04's `ptImg`), and `ImgCircle : Circle → Circle` for the circle carrying the
-- moved arc (Euclid superposes the SEGMENT; III.10 needs its circle — see the gap). Bodies sorry.
theorem proposition_24 : ∀ (a e b c f d : Point) (AB CD : Line) (AEB CFD : Circle),
  a.onCircle AEB ∧ e.onCircle AEB ∧ b.onCircle AEB ∧
  c.onCircle CFD ∧ f.onCircle CFD ∧ d.onCircle CFD ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  ¬ e.onLine AB ∧ ¬ f.onLine CD ∧
  -- on equal straight-lines
  |(a─b)| = |(c─d)| ∧
  -- similar segments (Def 3.11: "accepting equal angles")
  ∠ a:e:b = ∠ c:f:d →
  ⌓ a:e:b = ⌓ c:f:d :=
by
  euclid_intros
  euclid_intro_sentence "3.24.0"
    "Similar segments of circles on equal straight-lines are equal to one another. For let $AEB$ and $CFD$ be similar segments of circles on the equal straight-lines $AB$ and $CD$ (respectively). I say that segment $AEB$ is equal to segment $CFD$."

  -- Superposition: apply segment AEB onto CFD (A→C, chord AB laid along CD). `f` is the off-CD anchor
  -- so the moved arc point e' lands on the SAME side of CD as f. Outputs a' e' b' + circle AEB'
  -- carrying the moved arc. `ImgSegment`/`ImgCircle` are the concrete superposition maps (Prop04's
  -- `ptImg`/`lineImg` pattern) — the previous DEFERRED `sorry` maps were opaque and unprovable.
  euclid_apply (segment_superposition a e b c d f AB CD AEB) as (a', e', b', AEB')
  classical
  -- Distinctness among a, e, b (needed to simp the map). Derived BEFORE the function `let`s, because
  -- a function-typed local in context crashes the SMT translator behind euclid_finish.
  have h_ne_ea : e ≠ a := by euclid_finish
  have h_ne_ba : b ≠ a := by euclid_finish
  have h_ne_be : b ≠ e := by euclid_finish
  -- The moved image points/circle land on the circle AEB' (from formCircularSegment a' e' b' CD AEB').
  have hICa' : a'.onCircle AEB' := by euclid_finish
  have hICe' : e'.onCircle AEB' := by euclid_finish
  have hICb' : b'.onCircle AEB' := by euclid_finish

  let ImgSegment : Point → Point := fun p =>
    if p = a then a' else if p = e then e' else if p = b then b' else p
  let ImgCircle : Circle → Circle := fun L =>
    if L = AEB then AEB' else L

  have h_ImgSeg_a : ImgSegment a = a' := by simp (config := { zetaDelta := true })
  have h_ImgSeg_e : ImgSegment e = e' := by simp (config := { zetaDelta := true }) [h_ne_ea]
  have h_ImgSeg_b : ImgSegment b = b' := by
    simp (config := { zetaDelta := true }) [h_ne_ba, h_ne_be]
  have h_ImgCircle_AEB : ImgCircle AEB = AEB' := by simp (config := { zetaDelta := true })

  have hImgCircle :
      (ImgSegment a).onCircle (ImgCircle AEB) ∧ (ImgSegment e).onCircle (ImgCircle AEB) ∧ (ImgSegment b).onCircle (ImgCircle AEB) := by
    rw [h_ImgSeg_a, h_ImgSeg_e, h_ImgSeg_b, h_ImgCircle_AEB]
    exact ⟨hICa', hICe', hICb'⟩
  obtain ⟨hICa, hICe, hICb⟩ := hImgCircle

  -- the moved segment (image of AEB) and the target segment CFD, as objects
  let mseg := CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)
  let tseg := CircularSegment.ofPoints c f d

  -- @assumption_gap
  have step1_assumption1 : ImgSegment a = c := by euclid_apply (helper_3_24_step1_assumption1 a c a' (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show a' = c; assumption)))
  -- @assumption_gap
  have step1_assumption2 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD := by euclid_apply (helper_3_24_step1_assumption2 a b a' b' CD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show a'.onLine CD; assumption)) (by euclid_assumption "" (show b'.onLine CD; assumption)))
  -- @assumption_valid
  have step1_assumption3 : |(a─b)| = |(c─d)| := by assumption
  -- @assumption ("point $A$ is placed on (point) $C$", ImgSegment a = c)
  -- @assumption ("the straight-line $AB$ on $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  -- @assumption ("$AB$ being equal to $CD$", |(a─b)| = |(c─d)|)
  euclid_sentence "3.24.1"
    "For if the segment $AEB$ is applied to the segment $CFD$, and point $A$ is placed on (point) $C$, and the straight-line $AB$ on $CD$, (then) point $B$ will also coincide with point $D$, on account of $AB$ being equal to $CD$."
    (step1 : ImgSegment b = d) := by euclid_apply (helper_3_24_step1 a b c d a' b' CD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a'─b')|; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ¬ between b' c d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "point $A$ is placed on (point) $C$" (show ImgSegment a = c; assumption)) (by euclid_assumption "the straight-line $AB$ on $CD$" (show (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD; assumption)) (by euclid_assumption "$AB$ being equal to $CD$" (show |(a─b)| = |(c─d)|; assumption)))

  -- @assumption_valid
  have step2_assumption1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD := by assumption
  -- @assumption ("$AB$ coincides with $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  euclid_sentence "3.24.2"
    "And if $AB$ coincides with $CD$, (then) the segment $AEB$ will also coincide with $CFD$."
    (step2 : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD) := by euclid_apply (helper_3_24_step2 a e b c f d a' e' b' CD AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show a'.onCircle AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show b'.onCircle AEB'; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ¬ e'.onLine CD; assumption)) (by euclid_assumption "" (show ¬ f.onLine CD; assumption)) (by euclid_assumption "" (show c.onCircle CFD; assumption)) (by euclid_assumption "" (show f.onCircle CFD; assumption)) (by euclid_assumption "" (show d.onCircle CFD; assumption)) (by euclid_assumption "" (show e'.sameSide f CD; assumption)) (by euclid_assumption "" (show (∠ a':e':b' : ℝ) = (∠ a:e:b); assumption)) (by euclid_assumption "" (show (∠ a:e:b : ℝ) = (∠ c:f:d); assumption)) (by euclid_assumption "$AB$ coincides with $CD$" (show (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD; assumption)))

  have habsurd1 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)) := by
    intro hsuppose1
    -- @assumption_valid
    have step3_assumption1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD := by assumption
    -- @assumption_valid
    have step3_assumption2 : ¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD) := by assumption
    -- @assumption ("the straight-line $AB$ coincides with $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
    -- @assumption ("the segment $AEB$ does not coincide with $CFD$", ¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))
    euclid_sentence "3.24.3"
      "For if the straight-line $AB$ coincides with $CD$, and the segment $AEB$ does not coincide with $CFD$, (then) it will surely either fall inside it, outside (it),$^\\dag$ or it will miss like $CGD$ (in the figure),"
      (step3 : mseg.inside tseg ∨ mseg.outside tseg ∨ (¬ mseg.inside tseg ∧ ¬ mseg.outside tseg)) := by euclid_apply (helper_3_24_step3 a e b c f d CD CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "the straight-line $AB$ coincides with $CD$" (show (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD; assumption)) (by euclid_assumption "the segment $AEB$ does not coincide with $CFD$" (show ¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD); assumption)))

    -- Euclid's "miss" is the ONLY surviving case: the inside/outside (nesting) branches are excluded
    -- because the two segments have EQUAL inscribed angles (∠a:e:b = ∠c:f:d, the similar-segment
    -- hypothesis, carried to the moved segment). Two co-chordal same-side arcs with equal inscribed
    -- angle cannot nest — this is III.23-level content, NOT yet available as an axiom/prop in System E.
    -- These two obligations are what let step5 close all three branches of step3.
    have hnot_inside  : ¬ mseg.inside  tseg := by euclid_apply (helper_3_24_hnot_inside a e b c f d a' e' b' CD AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show a'.onCircle AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show b'.onCircle AEB'; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ¬ e'.onLine CD; assumption)) (by euclid_assumption "" (show ¬ f.onLine CD; assumption)) (by euclid_assumption "" (show c.onCircle CFD; assumption)) (by euclid_assumption "" (show f.onCircle CFD; assumption)) (by euclid_assumption "" (show d.onCircle CFD; assumption)) (by euclid_assumption "" (show e'.sameSide f CD; assumption)) (by euclid_assumption "" (show (∠ a':e':b' : ℝ) = (∠ a:e:b); assumption)) (by euclid_assumption "" (show (∠ a:e:b : ℝ) = (∠ c:f:d); assumption)))
    have hnot_outside : ¬ mseg.outside tseg := by euclid_apply (helper_3_24_hnot_outside a e b c f d a' e' b' CD AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show a'.onCircle AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show b'.onCircle AEB'; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ¬ e'.onLine CD; assumption)) (by euclid_assumption "" (show ¬ f.onLine CD; assumption)) (by euclid_assumption "" (show c.onCircle CFD; assumption)) (by euclid_assumption "" (show f.onCircle CFD; assumption)) (by euclid_assumption "" (show d.onCircle CFD; assumption)) (by euclid_assumption "" (show e'.sameSide f CD; assumption)) (by euclid_assumption "" (show (∠ a':e':b' : ℝ) = (∠ a:e:b); assumption)) (by euclid_assumption "" (show (∠ a:e:b : ℝ) = (∠ c:f:d); assumption)))

    -- @euclid_gap: Euclid superposes only the SEGMENT, but here invokes "a circle cuts another
    -- circle at >2 points" — a claim about CIRCLES (III.10). He silently carries the segment's
    -- circle (ImgCircle AEB) along without stating it. That unstated segment→circle move is the gap.
    euclid_sentence "3.24.4"
      "and a circle (will) cut (another) circle at more than two points."
      (step4 :
        (¬ mseg.inside tseg ∧ ¬ mseg.outside tseg) →
        ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p.onCircle (ImgCircle AEB) ∧ q.onCircle (ImgCircle AEB) ∧ r.onCircle (ImgCircle AEB) ∧
          p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD) := by euclid_apply (helper_3_24_step4 a e b c f d a' e' b' CD AB AEB AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Circle → Circle; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show ImgCircle AEB = AEB'; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show a'.onCircle AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show b'.onCircle AEB'; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ¬ e'.onLine CD; assumption)) (by euclid_assumption "" (show ¬ f.onLine CD; assumption)) (by euclid_assumption "" (show c.onCircle CFD; assumption)) (by euclid_assumption "" (show f.onCircle CFD; assumption)) (by euclid_assumption "" (show d.onCircle CFD; assumption)) (by euclid_assumption "" (show e'.sameSide f CD; assumption)))

    euclid_sentence "3.24.5"
      "The very thing is impossible [Prop.~3.10]."
      (step5 : False) := by euclid_apply (helper_3_24_step5 a e b c f d e' AEB AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Circle → Circle; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgCircle AEB = AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show ImgSegment a = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show ¬(ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD); assumption)) (by euclid_assumption "" (show ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d); assumption)) (by euclid_assumption "" (show ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d); assumption)) (by euclid_assumption "" (show (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d) ∧ ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)) → ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ p.onCircle (ImgCircle AEB) ∧ q.onCircle (ImgCircle AEB) ∧ r.onCircle (ImgCircle AEB) ∧ p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD; assumption)))
    exact step5

  -- @assumption_valid
  have step6_assumption1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD := by assumption
  -- @assumption ("the straight-line $AB$ is applied to $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  euclid_sentence "3.24.6"
    "Thus, if the straight-line $AB$ is applied to $CD$, the segment $AEB$ cannot not also coincide with $CFD$."
    (step6 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))) := by euclid_apply (helper_3_24_step6 a e b c d CD CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)); assumption)) (by euclid_assumption "the straight-line $AB$ is applied to $CD$" (show (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD; assumption)))

  euclid_sentence "3.24.7"
    "Thus, it will coincide,"
    (step7 : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD) := by euclid_apply (helper_3_24_step7 a e b c d CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)); assumption)))

  euclid_sentence "3.24.8"
    "and will be equal to it [C.N.~4]."
    (step8 : ⌓ a:e:b = ⌓ c:f:d) := by euclid_apply (helper_3_24_step8 a e b c f d a' e' b' CD AEB' CFD (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ImgSegment a = a'; assumption)) (by euclid_assumption "" (show ImgSegment e = e'; assumption)) (by euclid_assumption "" (show ImgSegment b = b'; assumption)) (by euclid_assumption "" (show a' = c; assumption)) (by euclid_assumption "" (show ImgSegment b = d; assumption)) (by euclid_assumption "" (show a'.onCircle AEB'; assumption)) (by euclid_assumption "" (show e'.onCircle AEB'; assumption)) (by euclid_assumption "" (show b'.onCircle AEB'; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ¬ e'.onLine CD; assumption)) (by euclid_assumption "" (show ¬ f.onLine CD; assumption)) (by euclid_assumption "" (show c.onCircle CFD; assumption)) (by euclid_assumption "" (show f.onCircle CFD; assumption)) (by euclid_assumption "" (show d.onCircle CFD; assumption)) (by euclid_assumption "" (show e'.sameSide f CD; assumption)) (by euclid_assumption "" (show (⌓ a':e':b' : ℝ) = (⌓ a:e:b); assumption)) (by euclid_assumption "" (show ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD; assumption)))

  exact step8
  euclid_conclude_sentence "3.24.9"
    "Thus, similar segments of circles on equal straight-lines are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
