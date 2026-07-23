import SystemE
import Book1.Prop04.Main
import Book1.Prop13.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option systemE.solverTime 30

-- Own namespace so this answer-key restatement of `proposition_5` does not collide with the real
-- `Elements.Book1.proposition_5` pulled in transitively by `Book1.Prop13.Main`'s dependency cone.
namespace AcceptV2
open Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "

  -- @assumption_valid
  have step1_assumption1 : |(a─b)| = |(a─c)| := by assumption
  -- @assumption ("the side $AB$ is equal to the side $AC$", |(a─b)| = |(a─c)|)
  euclid_sentence "1.5.1"
    "Since the side $AB$ is equal to the side $AC$, the base angles are equal to one another, so the angle $ABC$ is equal to the angle $ACB$."
    (step1 : ∠ a:b:c = ∠ a:c:b) := by
      euclid_apply (proposition_4 a b c a c b AB BC AC AC BC AB)
      euclid_finish

  -- @assumption_gap
  have step2_assumption1 : ∠ a:b:c + ∠ c:b:d = ∟ + ∟ := by
    euclid_apply (proposition_13 c b a d BC AB)
    euclid_finish
  -- @assumption_gap
  have step2_assumption2 : ∠ a:c:b + ∠ b:c:e = ∟ + ∟ := by
    euclid_apply (proposition_13 b c a e BC AC)
    euclid_finish
  -- @assumption_valid
  have step2_assumption3 : ∠ a:b:c = ∠ a:c:b := by assumption
  -- @assumption ("the angle $ABC$ together with the angle $CBD$ makes two right-angles", ∠ a:b:c + ∠ c:b:d = ∟ + ∟)
  -- @assumption ("the angle $ACB$ together with the angle $BCE$ makes two right-angles", ∠ a:c:b + ∠ b:c:e = ∟ + ∟)
  -- @assumption ("$ABC$ is equal to $ACB$", ∠ a:b:c = ∠ a:c:b)
  euclid_sentence "1.5.2"
    "Now, since the angle $ABC$ together with the angle $CBD$ makes two right-angles, and the angle $ACB$ together with the angle $BCE$ makes two right-angles, and since $ABC$ is equal to $ACB$, the remaining angle $CBD$ is equal to the remaining angle $BCE$."
    (step2 : ∠ c:b:d = ∠ b:c:e) := by euclid_finish

  euclid_sentence "1.5.3"
    "Thus, the angles at the base are equal to one another, and the angles under the base are equal to one another."
    (step3 : (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)) := by euclid_finish

  exact step3
  euclid_conclude_sentence "1.5.4"
    "(Which is) the very thing it was required to show."

end AcceptV2
