import SystemE
import Book3.Prop10.Main

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
  |(a─b)| = |(c─d)| ∧              -- on equal straight-lines
  ∠ a:e:b = ∠ c:f:d →              -- similar segments (Def 3.11: "accepting equal angles")
  ⌓ a:e:b = ⌓ c:f:d :=
by
  euclid_intros
  euclid_intro_sentence "3.24.0"
    "Similar segments of circles on equal straight-lines are equal to one another. For let $AEB$ and $CFD$ be similar segments of circles on the equal straight-lines $AB$ and $CD$ (respectively). I say that segment $AEB$ is equal to segment $CFD$."

  -- Superposition map + the circle carrying the moved arc (DEFERRED)
  have ImgSegment : Point → Point := by sorry
  have ImgCircle : Circle → Circle := by sorry
  have hImgCircle :
      (ImgSegment a).onCircle (ImgCircle AEB) ∧ (ImgSegment e).onCircle (ImgCircle AEB) ∧ (ImgSegment b).onCircle (ImgCircle AEB) := by sorry
  obtain ⟨hICa, hICe, hICb⟩ := hImgCircle

  -- @assumption ("point $A$ is placed on (point) $C$", ImgSegment a = c)
  -- @assumption ("the straight-line $AB$ on $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  -- @assumption ("$AB$ being equal to $CD$", |(a─b)| = |(c─d)|)
  euclid_sentence "3.24.1"
    "For if the segment $AEB$ is applied to the segment $CFD$, and point $A$ is placed on (point) $C$, and the straight-line $AB$ on $CD$, (then) point $B$ will also coincide with point $D$, on account of $AB$ being equal to $CD$."
    (step1 : ImgSegment b = d) := by sorry

  -- @assumption ("$AB$ coincides with $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  euclid_sentence "3.24.2"
    "And if $AB$ coincides with $CD$, (then) the segment $AEB$ will also coincide with $CFD$."
    (step2 : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD) := by sorry

  have habsurd1 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)) := by
    intro hsuppose1
    -- @assumption ("the straight-line $AB$ coincides with $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
    -- @assumption ("the segment $AEB$ does not coincide with $CFD$", ¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))
    euclid_sentence "3.24.3"
      "For if the straight-line $AB$ coincides with $CD$, and the segment $AEB$ does not coincide with $CFD$, (then) it will surely either fall inside it, outside (it),$^\\dag$ or it will miss like $CGD$ (in the figure),"
      (step3 :
        (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside  (CircularSegment.ofPoints c f d) ∨
        (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d) ∨
        (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside  (CircularSegment.ofPoints c f d) ∧
         ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d))) := by sorry

    -- @euclid_gap: Euclid superposes only the SEGMENT, but here invokes "a circle cuts another
    -- circle at >2 points" — a claim about CIRCLES (III.10). He silently carries the segment's
    -- circle (ImgCircle AEB) along without stating it. That unstated segment→circle move is the gap.
    euclid_sentence "3.24.4"
      "and a circle (will) cut (another) circle at more than two points."
      (step4 :
        (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside  (CircularSegment.ofPoints c f d) ∧
         ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)) →
        ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p.onCircle (ImgCircle AEB) ∧ q.onCircle (ImgCircle AEB) ∧ r.onCircle (ImgCircle AEB) ∧
          p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD) := by sorry

    euclid_sentence "3.24.5"
      "The very thing is impossible [Prop.~3.10]."
      (step5 : False) := by sorry
    exact step5

  -- @assumption ("the straight-line $AB$ is applied to $CD$", (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)
  euclid_sentence "3.24.6"
    "Thus, if the straight-line $AB$ is applied to $CD$, the segment $AEB$ cannot not also coincide with $CFD$."
    (step6 : ¬(¬ (ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))) := by sorry

  euclid_sentence "3.24.7"
    "Thus, it will coincide,"
    (step7 : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD) := by sorry

  euclid_sentence "3.24.8"
    "and will be equal to it [C.N.~4]."
    (step8 : ⌓ a:e:b = ⌓ c:f:d) := by sorry

  exact step8
  euclid_conclude_sentence "3.24.9"
    "Thus, similar segments of circles on equal straight-lines are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
