import SystemE
import Book1.Prop32.Main

set_option systemE.solverTime 30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace AcceptRefute
open Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "
  euclid_sentence "1.5.1"
    "For the angle $ABC$ is a right-angle, and the angle $ACB$ is also a right-angle."
    (step1 : (∠ a:b:c = ∟) ∧ (∠ a:c:b = ∟)) := by sorry

  have refute_step1 : ¬ ((∠ a:b:c = ∟) ∧ (∠ a:c:b = ∟)) := by
    euclid_apply (proposition_32 b a c e AB AC BC)
    euclid_finish

  -- @contradiction
  have contradiction: False := by
    apply refute_step1 step1

  euclid_sentence "1.5.2"
    "And therefore they are equal to one another [Post.~4]."
    (step2 : ∠ a:b:c = ∠ a:c:b) := by sorry

  euclid_sentence "1.5.3"
    "Likewise, the angle $CBD$ is a right-angle, and the angle $BCE$ is a right-angle."
    (step3 : (∠ c:b:d = ∟) ∧ (∠ b:c:e = ∟)) := by sorry

  euclid_sentence "1.5.4"
    "And so these also are equal to one another [Post.~4]."
    (step4 : ∠ c:b:d = ∠ b:c:e) := by sorry

  euclid_sentence "1.5.5"
    "Thus, the angles at the base are equal to one another, and the angles under the base are equal to one another."
    (step5 : (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)) := by sorry

  exact step5
  euclid_conclude_sentence "1.5.6"
    "(Which is) the very thing it was required to show."

end AcceptRefute
