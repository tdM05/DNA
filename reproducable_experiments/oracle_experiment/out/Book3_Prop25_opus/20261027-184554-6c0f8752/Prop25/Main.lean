import SystemE
import Book1.Prop10.Main
import Book1.Prop23.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_25 : ∀ (a b c : Point) (AC : Line),
  a.onLine AC ∧ c.onLine AC ∧ a ≠ c ∧ ¬b.onLine AC ∧ |(a─b)| = |(c─b)| →
  ∃ (α : Circle), a.onCircle α ∧ b.onCircle α ∧ c.onCircle α := by
  euclid_intros
  euclid_intro_sentence "3.25.0"
    "For a given segment of a circle, to complete the circle, the very one of which it is a segment. Let $ABC$ be the given segment of a circle. So it is required to complete the circle for segment $ABC$, the very one of which it is a segment."

  euclid_apply (proposition_10 a c AC) as d
  euclid_sentence "3.25.1"
    "For let $AC$ be cut in half at (point) $D$ [Prop.~1.10],"
    (step1 : between a d c ∧ |(a─d)| = |(d─c)|) := by sorry

  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.25.2"
    "and let $DB$ be drawn from point $D$, at right-angles to $AC$ [Prop.~1.11]."
    (step2 : ∠ a:d:b = ∟) := by sorry

  euclid_apply (line_from_points a b) as AB
  euclid_sentence "3.25.3"
    "And let $AB$ be joined."
    (step3 : distinctPointsOnLine a b AB) := by sorry

  euclid_sentence "3.25.4"
    "Thus, angle $ABD$ is surely either greater than, equal to, or less than (angle) $BAD$."
    (step4 : ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d) := by sorry

  rcases step4 with hgt | heq | hlt
  · -- CASE 1 : ∠ABD greater than ∠BAD (centre E outside the segment)
    euclid_sentence "3.25.5"
      "First of all, let it be greater."
      (step5 : ∠ a:b:d > ∠ b:a:d) := by sorry

    have hra1 : formRectilinearAngle a b d AB DB := by sorry
    euclid_apply (proposition_23 a b b a d AB AB DB) as e0
    euclid_apply (line_from_points a e0) as AE
    euclid_sentence "3.25.6"
      "And let (angle) $BAE$, equal to angle $ABD$, be constructed on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]."
      (step6 : ∠ b:a:e0 = ∠ a:b:d) := by sorry

    have hint1 : DB.intersectsLine AE := by sorry
    euclid_apply (intersection_lines DB AE) as e
    euclid_sentence "3.25.7"
      "And let $DB$ be drawn through to $E$,"
      (step7 : e.onLine DB) := by sorry

    have hec : e ≠ c := by sorry
    euclid_apply (line_from_points e c) as EC
    euclid_sentence "3.25.8"
      "and let $EC$ be joined."
      (step8 : distinctPointsOnLine e c EC) := by sorry

    -- @assumption ("angle $ABE$ is equal to $BAE$", ∠ a:b:e = ∠ b:a:e)
    euclid_sentence "3.25.9"
      "Therefore, since angle $ABE$ is equal to $BAE$, the straight-line $EB$ is thus also equal to $EA$ [Prop.~1.6]."
      (step9 : |(e─b)| = |(e─a)|) := by sorry

    -- @assumption ("$AD$ is equal to $DC$", |(a─d)| = |(d─c)|)
    -- @assumption ("$DE$ (is) common", |(d─e)| = |(d─e)|)
    euclid_sentence "3.25.10"
      "And since $AD$ is equal to $DC$, and $DE$ (is) common, the two (straight-lines) $AD$, $DE$ are equal to the two (straight-lines) $CD$, $DE$, respectively."
      (step10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) := by sorry

    -- @assumption ("each (is) a right-angle", ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    euclid_sentence "3.25.11"
      "And angle $ADE$ is equal to angle $CDE$. For each (is) a right-angle."
      (step11 : ∠ a:d:e = ∠ c:d:e) := by sorry

    euclid_sentence "3.25.12"
      "Thus, the base $AE$ is equal to the base $CE$ [Prop.~1.4]."
      (step12 : |(a─e)| = |(c─e)|) := by sorry

    -- @assumption ("$AE$ was shown (to be) equal to $BE$", |(a─e)| = |(b─e)|)
    euclid_sentence "3.25.13"
      "But, $AE$ was shown (to be) equal to $BE$. Thus, $BE$ is also equal to $CE$."
      (step13 : |(b─e)| = |(c─e)|) := by sorry

    euclid_sentence "3.25.14"
      "Thus, the three (straight-lines) $AE$, $EB$, and $EC$ are equal to one another."
      (step14 : |(e─a)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) := by sorry

    have hea : e ≠ a := by sorry
    euclid_apply (circle_from_points e a) as alpha
    euclid_sentence "3.25.15"
      "Thus, if a circle is drawn with center $E$, and radius one of $AE$, $EB$, or $EC$, it will also go through the remaining points (of the segment), and the (associated circle) will be completed [Prop.~3.9]."
      (step15 : e.isCentre alpha ∧ a.onCircle alpha ∧ b.onCircle alpha ∧ c.onCircle alpha) := by sorry

    euclid_sentence "3.25.16"
      "Thus, a circle has been completed from the given segment of a circle."
      (step16 : ∃ (α : Circle), a.onCircle α ∧ b.onCircle α ∧ c.onCircle α) := by sorry

    euclid_sentence "3.25.17"
      "And (it is) clear that the segment $ABC$ is less than a semi-circle, because the center $E$ happens to lie outside it."
      (step17 : e.opposingSides b AC) := by sorry

    exact step16
  · -- CASE 2 : ∠ABD equal to ∠BAD (centre is D; AC is a diameter)
    -- @assumption ("angle $ABD$ is equal to $BAD$", ∠ a:b:d = ∠ b:a:d)
    -- @assumption ("$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$", |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
    euclid_sentence "3.25.18"
      "[And], similarly, even if angle $ABD$ is equal to $BAD$, (since) $AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$, the three (straight-lines) $DA$, $DB$, and $DC$ will be equal to one another."
      (step18 : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)|) := by sorry

    have hda : d ≠ a := by sorry
    euclid_apply (circle_from_points d a) as alpha2
    euclid_sentence "3.25.19"
      "And point $D$ will be the center of the completed circle."
      (step19 : d.isCentre alpha2 ∧ a.onCircle alpha2 ∧ b.onCircle alpha2 ∧ c.onCircle alpha2) := by sorry

    euclid_sentence "3.25.20"
      "And $ABC$ will manifestly be a semi-circle."
      (step20 : ∃ (o : Point), o.isCentre alpha2 ∧ between a o c ∧ a.onCircle alpha2 ∧ c.onCircle alpha2) := by sorry

    exact ⟨alpha2, step19.2.1, step19.2.2.1, step19.2.2.2⟩
  · -- CASE 3 : ∠ABD less than ∠BAD (centre on DB, inside the segment)
    -- @assumption ("$ABD$ is less than $BAD$", ∠ a:b:d < ∠ b:a:d)
    have hra3 : formRectilinearAngle a b d AB DB := by sorry
    euclid_apply (proposition_23 a b b a d AB AB DB) as e0p
    euclid_apply (line_from_points a e0p) as AEp
    have hint3 : DB.intersectsLine AEp := by sorry
    euclid_apply (intersection_lines DB AEp) as e3
    euclid_sentence "3.25.21"
      "And if $ABD$ is less than $BAD$, and we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23], then the center will fall on $DB$, inside the segment $ABC$."
      (step21 : e3.onLine DB ∧ e3.sameSide b AC) := by sorry

    euclid_sentence "3.25.22"
      "And segment $ABC$ will manifestly be greater than a semi-circle."
      (step22 : e3.sameSide b AC) := by sorry

    have hcirc3 : ∃ (α : Circle), a.onCircle α ∧ b.onCircle α ∧ c.onCircle α := by sorry
    exact hcirc3

  euclid_conclude_sentence "3.25.23"
    "Thus, a circle has been completed from the given segment of a circle. (Which is) the very thing it was required to do."

end Elements.Book3
