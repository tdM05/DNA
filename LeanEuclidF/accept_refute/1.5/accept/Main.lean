import SystemE
import Book1.Prop04.Main
import Book1.Prop13.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option systemE.solverTime 30

-- Own namespace so this answer-key restatement of `proposition_5` does not collide with the real
-- `Elements.Book1.proposition_5` pulled in transitively by `Book1.Prop13.Main`'s dependency cone.
namespace AcceptV5
open Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "

  -- @assumption ("$AB$ is equal to $AC$", |(a─b)| = |(a─c)|)
  -- Pappus's self-comparison: pair the two vertex-A sides of △ABC and △ACB.
  euclid_sentence "1.5.1"
    "For since $AB$ is equal to $AC$, and $AC$ to $AB$, the two (straight-lines) $BA$, $AC$ are equal to the two (straight-lines) $CA$, $AB$, respectively."
    (step1 : (|(b─a)| = |(c─a)|) ∧ (|(a─c)| = |(a─b)|)) := by euclid_finish

  -- The common included angle: △ABC's angle at A (∠BAC) is △ACB's angle at A (∠CAB).
  euclid_sentence "1.5.2"
    "And they encompass a common angle, $BAC$."
    (step2 : ∠ b:a:c = ∠ c:a:b) := by euclid_finish

  -- SAS [Prop.~1.4] on △ABC vs △ACB (A↔A, B↔C, C↔B).
  euclid_sentence "1.5.3"
    "Thus, comparing triangle $ABC$ with triangle $ACB$, the base $BC$ is equal to the base $CB$, and the remaining angles subtended by the equal sides are equal to the corresponding remaining angles [Prop.~1.4]."
    (step3 : (|(b─c)| = |(c─b)|) ∧ (∠ a:b:c = ∠ a:c:b)) := by
      euclid_apply (proposition_4 a b c a c b AB BC AC AC BC AB)
      euclid_finish

  euclid_sentence "1.5.4"
    "Thus, the angle $ABC$, subtended by $AC$, is equal to the angle $ACB$, subtended by $AB$."
    (step4 : ∠ a:b:c = ∠ a:c:b) := by euclid_finish

  -- "at the base": ∠ABC, ∠ACB already ARE the base angles → conclusion 1.
  euclid_sentence "1.5.5"
    "And these are at the base of triangle $ABC$."
    (step5 : ∠ a:b:c = ∠ a:c:b) := by euclid_finish

  -- @assumption ("$BD$ has been produced in a straight-line with $AB$", between a b d)
  euclid_sentence "1.5.6"
    "Again, since $BD$ has been produced in a straight-line with $AB$, the points $A$, $B$, $D$ lie on a straight-line."
    (step6 : a.onLine AB ∧ b.onLine AB ∧ d.onLine AB) := by euclid_finish

  -- Straight-line CB on the straight AD makes the two adjacent angles two right-angles [Prop.~1.13].
  euclid_sentence "1.5.7"
    "Thus, the straight-line $CB$, standing on the straight-line $AD$, makes the (sum of the) adjacent angles $ABC$ and $CBD$ equal to two right-angles [Prop.~1.13]."
    (step7 : ∠ a:b:c + ∠ c:b:d = ∟ + ∟) := by
      euclid_apply (proposition_13 c b a d BC AB)
      euclid_finish

  -- @assumption ("$CE$ has been produced in a straight-line with $AC$", between a c e)
  euclid_sentence "1.5.8"
    "So too, since $CE$ has been produced in a straight-line with $AC$, the points $A$, $C$, $E$ lie on a straight-line, and the straight-line $BC$, standing on the straight-line $AE$, makes the (sum of the) adjacent angles $ACB$ and $BCE$ equal to two right-angles [Prop.~1.13]."
    (step8 : (a.onLine AC ∧ c.onLine AC ∧ e.onLine AC) ∧ (∠ a:c:b + ∠ b:c:e = ∟ + ∟)) := by
      euclid_apply (proposition_13 b c a e BC AC)
      euclid_finish

  euclid_sentence "1.5.9"
    "Thus, the (sum of the angles) $ABC$ and $CBD$ is equal to the (sum of the angles) $ACB$ and $BCE$."
    (step9 : ∠ a:b:c + ∠ c:b:d = ∠ a:c:b + ∠ b:c:e) := by euclid_finish

  euclid_sentence "1.5.10"
    "And of these, the angle $ABC$ was shown to be equal to the angle $ACB$."
    (step10 : ∠ a:b:c = ∠ a:c:b) := by euclid_finish

  -- Subtract the equal base angles from the equal straight-angle sums [C.N.~3] → conclusion 2.
  euclid_sentence "1.5.11"
    "Thus, the remaining angle $CBD$ is equal to the remaining angle $BCE$ [C.N.~3]."
    (step11 : ∠ c:b:d = ∠ b:c:e) := by euclid_finish

  -- "under the base": ∠CBD, ∠BCE already ARE the under-base angles.
  euclid_sentence "1.5.12"
    "And these are under the base."
    (step12 : ∠ c:b:d = ∠ b:c:e) := by euclid_finish

  exact ⟨step5, step11⟩
  euclid_conclude_sentence "1.5.13"
    "Thus, for isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. (Which is) the very thing it was required to show."

end AcceptV5
