import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "

  -- @assumption ("the side $AB$ is equal to the side $AC$", |(a─b)| = |(a─c)|)
  -- ⚠ MIXED STEP — our sufficient condition is STUCK here:
  --   • cannot ACCEPT: `|(b─c)| = |(a─b)|` is NOT entailed by H (a non-equilateral isosceles
  --     triangle satisfies H); `euclid_finish` returns "Could not prove".
  --   • cannot REFUTE: `¬(|(b─c)| = |(a─b)|)` is NOT a theorem either (an equilateral triangle
  --     satisfies H AND this equality); `euclid_finish` returns "Could not prove: False".
  --   To reject it you must exhibit an explicit COUNTERMODEL `∃ config, H ∧ |(b─c)| ≠ |(a─b)|`
  --   (a concrete non-equilateral isosceles triangle) — i.e. drop to coordinates / build a model.
  euclid_sentence "1.5.1"
    "Since the side $AB$ is equal to the side $AC$, and the base $BC$ is equal to the side $AB$, the triangle $ABC$ is equilateral."
    (step1 : |(b─c)| = |(a─b)|) := by sorry

  euclid_sentence "1.5.2"
    "And in an equilateral triangle all three angles are equal to one another, so in particular the angle $ABC$ is equal to the angle $ACB$."
    (step2 : ∠ a:b:c = ∠ a:c:b) := by sorry

  -- @assumption ("the points $A$, $B$, $D$ lie in a straight line", between a b d)
  -- @assumption ("likewise $A$, $C$, $E$", between a c e)
  euclid_sentence "1.5.3"
    "And since the points $A$, $B$, $D$ lie in a straight line, and likewise $A$, $C$, $E$, the angles $CBD$ and $BCE$, being the supplements of the equal angles $ABC$ and $ACB$, are equal to one another."
    (step3 : ∠ c:b:d = ∠ b:c:e) := by sorry

  euclid_sentence "1.5.4"
    "Thus, the angles at the base are equal to one another, and the angles under the base are equal to one another."
    (step4 : (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)) := by sorry

  exact step4
  euclid_conclude_sentence "1.5.5"
    "(Which is) the very thing it was required to show."

end Elements.Book1
