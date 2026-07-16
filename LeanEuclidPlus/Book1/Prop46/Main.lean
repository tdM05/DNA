import SystemE
import Book1Variants.Prop11
import Book1.Prop03.Main
import Book1.Prop31.Main

namespace Elements.Book1

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.46.0"
    "To describe a square on a given straight-line. Let $AB$ be the given straight-line. So it is required to describe a square on the straight-line $AB$. "

  euclid_apply (extend_point AB b a) as g
  euclid_apply (proposition_11 b g a AB) as c
  euclid_apply (line_from_points a c) as AC
  euclid_sentence "1.46.1"
    "Let $AC$ have been drawn at right-angles to the straight-line $AB$ from the point $A$ on it [Prop.~1.11],"
    (step1 : ∠ c:a:b = ∟) := by sorry

  euclid_apply (extend_point_longer AC a c (a─b)) as c1
  euclid_apply (proposition_3 a c1 a b AC AB) as d
  euclid_apply (line_from_points a d) as AD
  euclid_sentence "1.46.2"
    "and let $AD$ have been made equal to $AB$ [Prop.~1.3]."
    (step2 : |(a─d)| = |(a─b)|) := by sorry

  euclid_apply (proposition_31 d a b AB) as DE
  euclid_sentence "1.46.3"
    "And let $DE$ have been drawn through point $D$ parallel to $AB$ [Prop.~1.31],"
    (step3 : d.onLine DE ∧ ¬(DE.intersectsLine AB)) := by sorry

  euclid_apply (proposition_31 b a d AD) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_sentence "1.46.4"
    "and let $BE$ have been drawn through point $B$ parallel to $AD$ [Prop.~1.31]."
    (step4 : b.onLine BE ∧ ¬(BE.intersectsLine AD)) := by sorry

  euclid_sentence "1.46.5"
    "Thus, $ADEB$ is a parallelogram."
    (step5 : formParallelogram d e a b DE AB AD BE) := by sorry

  euclid_sentence "1.46.6"
    "Therefore, $AB$ is equal to $DE$,"
    (step6 : |(a─b)| = |(d─e)|) := by sorry

  euclid_sentence "1.46.7"
    "and $AD$ to $BE$ [Prop.~1.34]."
    (step7 : |(a─d)| = |(b─e)|) := by sorry

  euclid_sentence "1.46.8"
    "But, $AB$ is equal to $AD$."
    (step8 : |(a─b)| = |(a─d)|) := by sorry

  euclid_sentence "1.46.9"
    "Thus, the four (sides) $BA$, $AD$, $DE$, and $EB$ are equal to one another."
    (step9 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by sorry

  euclid_sentence "1.46.10"
    "Thus, the parallelogram $ADEB$ is equilateral."
    (step10 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by sorry

  euclid_wts "1.46.11"
    "So I say that (it is) also right-angled."

  -- @assumption_valid
  have step12_assumption1 : ¬(DE.intersectsLine AB) := by assumption
  -- @assumption ("the straight-line $AD$ falls across the parallels $AB$ and $DE$", ¬(DE.intersectsLine AB))
  euclid_sentence "1.46.12"
    "For since the straight-line $AD$ falls across the parallels $AB$ and $DE$, the (sum of the) angles $BAD$ and $ADE$ is equal to two right-angles [Prop.~1.29]."
    (step12 : ∠ b:a:d + ∠ a:d:e = ∟ + ∟) := by sorry

  euclid_sentence "1.46.13"
    "But $BAD$ (is a) right-angle."
    (step13 : ∠ b:a:d = ∟) := by sorry

  euclid_sentence "1.46.14"
    "Thus, $ADE$ (is) also a right-angle."
    (step14 : ∠ a:d:e = ∟) := by sorry

  euclid_sentence "1.46.15"
    "And for parallelogrammic figures, the opposite sides and angles are equal to one another [Prop.~1.34]."
    (step15 : formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e)) := by sorry

  euclid_sentence "1.46.16"
    "Thus, each of the opposite angles $ABE$ and $BED$ (are) also right-angles."
    (step16 : ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) := by sorry

  euclid_sentence "1.46.17"
    "Thus, $ADEB$ is right-angled."
    (step17 : ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) := by sorry

  euclid_sentence "1.46.18"
    "And it was also shown (to be) equilateral.  "
    (step18 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by sorry

  euclid_sentence "1.46.19"
    "Thus, ($ADEB$) is a square [Def.~1.22]."
    (step19 : (|(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) ∧
      (∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟)) := by sorry

  have hbe : |(b─e)| = |(a─b)| := by sorry
  exact ⟨d, e, DE, AD, BE, step5, step6.symm, step2, hbe, step13, step14, step16.1, step16.2⟩
  euclid_conclude_sentence "1.46.20"
    "And it is described on the straight-line $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
