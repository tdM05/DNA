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

  -- @assumption ("the side $AB$ is equal to the side $AC$", |(a─b)| = |(a─c)|)
  euclid_sentence "1.5.1"
    "Since the side $AB$ is equal to the side $AC$, the base angles are equal to one another, so the angle $ABC$ is equal to the angle $ACB$."
    (step1 : ∠ a:b:c = ∠ a:c:b) := by sorry

  -- @assumption ("the points $A$, $B$, $D$ lie in a straight line", between a b d)
  -- @assumption ("likewise $A$, $C$, $E$", between a c e)
  euclid_sentence "1.5.2"
    "And since the points $A$, $B$, $D$ lie in a straight line, and likewise $A$, $C$, $E$, the angle $ABC$ together with $CBD$ makes two right-angles, and the angle $ACB$ together with $BCE$ makes two right-angles."
    (step2 : (∠ a:b:c + ∠ c:b:d = ∟ + ∟) ∧ (∠ a:c:b + ∠ b:c:e = ∟ + ∟)) := by sorry

  euclid_sentence "1.5.3"
    "Now the angle $CBD$ is itself a right-angle, since $BC$ stands upon the straight-line $AD$."
    (step3 : ∠ c:b:d = ∟) := by sorry

  have refute_step3 : ¬ (∠ c:b:d = ∟) := by
    euclid_apply (proposition_32 c a b d AC AB BC)
    euclid_finish

  -- @contradiction
  have contradiction : False := by
    apply refute_step3 step3

  euclid_sentence "1.5.4"
    "And in the same way the angle $BCE$ is a right-angle."
    (step4 : ∠ b:c:e = ∟) := by sorry

  euclid_sentence "1.5.5"
    "Therefore the angle $CBD$ is equal to the angle $BCE$, each being a right-angle."
    (step5 : ∠ c:b:d = ∠ b:c:e) := by sorry

  euclid_sentence "1.5.6"
    "Thus, the angles at the base are equal to one another, and the angles under the base are equal to one another."
    (step6 : (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)) := by sorry

  exact step6
  euclid_conclude_sentence "1.5.7"
    "(Which is) the very thing it was required to show."

end AcceptRefute
