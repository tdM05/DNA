import SystemE
import Book3.Prop01.Main

namespace Elements.Book3

theorem proposition_4 : ∀ (a b c d e f : Point) (AC BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  f.isCentre ABCD ∧ ¬f.onLine AC ∧ ¬f.onLine BD ∧
  AC ≠ BD ∧ between a e c ∧ between b e d →
  ¬(|(a─e)| = |(e─c)| ∧ |(b─e)| = |(e─d)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.4.0"
    "In a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. Let $ABCD$ be a circle, and within it, let two straight-lines, $AC$ and $BD$, which are not through the center, cut one another at (point) $E$. I say that they do not cut one another in half."

  euclid_sentence "3.4.1"
    "For, if possible, let them cut one another in half, such that $AE$ is equal to $EC$,"
    (step1 : |(a─e)| = |(e─c)|) := by sorry

  euclid_sentence "3.4.2"
    "and $BE$ to $ED$."
    (step2 : |(b─e)| = |(e─d)|) := by sorry

  -- note this is redundant, but faithful. Euclid is justifying how we construct the center, not that it exists, since existence is assumed.
  euclid_apply (proposition_1 ABCD) as f'
  euclid_sentence "3.4.3"
    "And let the center of the circle $ABCD$ be found [Prop.~3.1], and let it be (at point) $F$,"
    (step3 : f'.isCentre ABCD ∧ f' = f) := by sorry

  euclid_apply (line_from_points f e) as FE
  euclid_sentence "3.4.4"
    "and let $FE$ be joined."
    (step4 : distinctPointsOnLine f e FE) := by sorry

  -- @assumption_valid
  have step5_assumption1 : |(a─e)| = |(e─c)| := by assumption
  -- @assumption ("some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$", |(a─e)| = |(e─c)|)
  euclid_sentence "3.4.5"
    "Therefore, since some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$, it also cuts it at right-angles [Prop.~3.3]."
    (step5 : ∠ f:e:a = ∟) := by sorry

  euclid_sentence "3.4.6"
    "Thus, $FEA$ is a right-angle."
    (step6 : ∠ f:e:a = ∟) := by sorry

  -- @assumption_valid
  have step7_assumption1 : |(b─e)| = |(e─d)| := by assumption
  -- @assumption ("some straight-line $FE$ cuts in half some straight-line $BD$", |(b─e)| = |(e─d)|)
  euclid_sentence "3.4.7"
    "Again, since some straight-line $FE$ cuts in half some straight-line $BD$, it also cuts it at right-angles [Prop.~3.3]."
    (step7 : ∠ f:e:b = ∟) := by sorry

  euclid_sentence "3.4.8"
    "Thus, $FEB$ (is) a right-angle."
    (step8 : ∠ f:e:b = ∟) := by sorry

  -- @assumption_valid
  have step9_assumption1 : ∠ f:e:a = ∟ := by assumption
  -- @assumption ("But $FEA$ was also shown (to be) a right-angle", ∠ f:e:a = ∟)
  euclid_sentence "3.4.9"
    "But $FEA$ was also shown (to be) a right-angle. Thus, $FEA$ (is) equal to $FEB$, the lesser to the greater."
    (step9 : ∠ f:e:a = ∠ f:e:b) := by sorry

  -- @euclid_gap: Euclid says "two straight-lines that cut one another" (implicitly AC≠BD).
  -- Without AC≠BD, the degenerate AC=BD case is a counterexample (same chord given twice,
  -- both bisected at e). Fixed by adding AC≠BD to the signature.
  euclid_sentence "3.4.10"
    "The very thing is impossible."
    (step10 : False) := by sorry

  exact step10
  euclid_conclude_sentence "3.4.11"
    "Thus, $AC$ and $BD$ do not cut one another in half."
  euclid_conclude_sentence "3.4.12"
    "Thus, in a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. (Which is) the very thing it was required to show."

end Elements.Book3
