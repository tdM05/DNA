import SystemE
import Book1.Prop10.Main
import Book1Variants.Prop23

namespace Elements.Book3

open Elements.Book1

-- orchestrator-agreed: construction — a given segment (3 non-collinear points: chord AC + arc point b) → ∃ the completed
-- circle through all three. Clean, proof-faithful (proof exhibits center, [3.9] completes; final sentence = the ∃).
theorem proposition_25 : ∀ (a b c : Point) (AC : Line),
  a.onLine AC ∧ c.onLine AC ∧ a ≠ c ∧ ¬b.onLine AC ∧ |(a─b)| = |(c─b)| →
  ∃ (α : Circle), a.onCircle α ∧ b.onCircle α ∧ c.onCircle α :=
by
  euclid_intros
  euclid_intro_sentence "3.25.0"
    "For a given segment of a circle, to complete the circle, the very one of which it is a segment. Let $ABC$ be the given segment of a circle. So it is required to complete the circle for segment $ABC$, the very one of which it is a segment."

  euclid_apply (proposition_10 a c AC) as d
  euclid_apply (line_from_points d b) as DB
  euclid_apply (line_from_points a b) as AB

  euclid_sentence "3.25.1"
    "For let $AC$ be cut in half at (point) $D$ [Prop.~1.10],"
    (step1 : between a d c ∧ |(a─d)| = |(d─c)|) := by sorry

  euclid_sentence "3.25.2"
    "and let $DB$ be drawn from point $D$, at right-angles to $AC$ [Prop.~1.11]."
    (step2 : ∠ a:d:b = ∟) := by sorry

  euclid_sentence "3.25.3"
    "And let $AB$ be joined."
    (step3 : distinctPointsOnLine a b AB) := by sorry

  euclid_sentence "3.25.4"
    "Thus, angle $ABD$ is surely either greater than, equal to, or less than (angle) $BAD$."
    (step4 : ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d) := by sorry

  by_cases hgt : ∠ a:b:d > ∠ b:a:d
  ·
    euclid_sentence "3.25.5"
      "First of all, let it be greater."
      (step5 : ∠ a:b:d > ∠ b:a:d) := by sorry

    euclid_apply (proposition_23' a b b a d d AB AB DB) as g
    euclid_apply (line_from_points a g) as AG
    have hAGDB : AG.intersectsLine DB := by sorry
    euclid_apply (intersection_lines AG DB) as e
    have hec : e ≠ c := by sorry
    euclid_apply (line_from_points e c) as EC
    euclid_apply (circle_from_points e a) as α₁

    euclid_sentence "3.25.6"
      "And let (angle) $BAE$, equal to angle $ABD$, be constructed on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]."
      (step6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) := by sorry

    euclid_sentence "3.25.7"
      "And let $DB$ be drawn through to $E$,"
      (step7 : e.onLine DB) := by sorry

    euclid_sentence "3.25.8"
      "and let $EC$ be joined."
      (step8 : distinctPointsOnLine e c EC) := by sorry

    -- @assumption_gap
    have step9_assumption1 : ∠ a:b:e = ∠ b:a:e := by sorry
    -- @assumption ("angle $ABE$ is equal to $BAE$", ∠ a:b:e = ∠ b:a:e)
    euclid_sentence "3.25.9"
      "Therefore, since angle $ABE$ is equal to $BAE$, the straight-line $EB$ is thus also equal to $EA$ [Prop.~1.6]."
      (step9 : |(e─b)| = |(e─a)|) := by sorry

    -- @assumption_valid
    have step10_assumption1 : |(a─d)| = |(d─c)| := by assumption
    -- @assumption_valid
    have step10_assumption2 : |(d─e)| = |(d─e)| := by rfl
    -- @assumption ("$AD$ is equal to $DC$", |(a─d)| = |(d─c)|)
    -- @assumption ("$DE$ (is) common", |(d─e)| = |(d─e)|)
    euclid_sentence "3.25.10"
      "And since $AD$ is equal to $DC$, and $DE$ (is) common, the two (straight-lines) $AD$, $DE$ are equal to the two (straight-lines) $CD$, $DE$, respectively."
      (step10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) := by sorry

    -- @assumption_valid
    have step11_assumption1 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟ := by euclid_finish
    -- @assumption ("For each (is) a right-angle", ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    euclid_sentence "3.25.11"
      "And angle $ADE$ is equal to angle $CDE$. For each (is) a right-angle."
      (step11 : ∠ a:d:e = ∠ c:d:e) := by sorry

    euclid_sentence "3.25.12"
      "Thus, the base $AE$ is equal to the base $CE$ [Prop.~1.4]."
      (step12 : |(a─e)| = |(c─e)|) := by sorry

    euclid_sentence "3.25.13"
      "But, $AE$ was shown (to be) equal to $BE$."
      (step13 : |(a─e)| = |(b─e)|) := by sorry

    euclid_sentence "3.25.14"
      "Thus, $BE$ is also equal to $CE$."
      (step14 : |(b─e)| = |(c─e)|) := by sorry

    euclid_sentence "3.25.15"
      "Thus, the three (straight-lines) $AE$, $EB$, and $EC$ are equal to one another."
      (step15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) := by sorry

    euclid_sentence "3.25.16"
      "Thus, if a circle is drawn with center $E$, and radius one of $AE$, $EB$, or $EC$, it will also go through the remaining points (of the segment), and the (associated circle) will be completed [Prop.~3.9]."
      (step16 : e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) := by sorry

    euclid_sentence "3.25.17"
      "Thus, a circle has been completed from the given segment of a circle."
      (step17 : a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) := by sorry

    -- @assumption_valid
    have step18_assumption1 : e.opposingSides b AC := by euclid_finish
    -- @assumption ("because the center $E$ happens to lie outside it", e.opposingSides b AC)
    euclid_sentence "3.25.18"
      "And (it is) clear that the segment $ABC$ is less than a semi-circle, because the center $E$ happens to lie outside it."
      (step18 : e.opposingSides b AC) := by sorry

    exact ⟨α₁, step17⟩

  · by_cases heq : ∠ a:b:d = ∠ b:a:d
    ·
      -- @assumption_valid
      have step19_assumption1 : ∠ a:b:d = ∠ b:a:d := by assumption
      -- @assumption_valid
      have step19_assumption2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)| := by euclid_finish
      -- @assumption ("angle $ABD$ is equal to $BAD$", ∠ a:b:d = ∠ b:a:d)
      -- @assumption ("$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$", |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
      euclid_sentence "3.25.19"
        "[And], similarly, even if angle $ABD$ is equal to $BAD$, (since) $AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$, the three (straight-lines) $DA$, $DB$, and $DC$ will be equal to one another."
        (step19 : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)|) := by sorry

      -- D is the center; introduce circle α₂ with center D, point A on it
      have hda : d ≠ a := by sorry
      euclid_apply (circle_from_points d a) as α₂

      euclid_sentence "3.25.20"
        "And point $D$ will be the center of the completed circle."
        (step20 : d.isCentre α₂) := by sorry

      -- semicircle: center D lies between A and C on the chord (diameter)
      euclid_sentence "3.25.21"
        "And $ABC$ will manifestly be a semi-circle."
        (step21 : between a d c ∧ d.isCentre α₂) := by sorry

      use α₂
      have haα₂ : a.onCircle α₂ := by sorry
      have hbα₂ : b.onCircle α₂ := by sorry
      have hcα₂ : c.onCircle α₂ := by sorry
      exact ⟨haα₂, hbα₂, hcα₂⟩

    -- Case 3: ∠ABD < ∠BAD
    ·
      euclid_apply (proposition_23' a b b a d d AB AB DB) as g3
      euclid_apply (line_from_points a g3) as AG3
      have hAG3DB : AG3.intersectsLine DB := by sorry
      euclid_apply (intersection_lines AG3 DB) as e
      euclid_apply (circle_from_points e a) as α₃

      -- @assumption_valid
      have step22_assumption1 : ∠ a:b:d < ∠ b:a:d := by euclid_finish
      -- @assumption ("$ABD$ is less than $BAD$", ∠ a:b:d < ∠ b:a:d)
      euclid_sentence "3.25.22"
        "And if $ABD$ is less than $BAD$, and we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23], then the center will fall on $DB$, inside the segment $ABC$."
        (step22 : e.onLine DB ∧ e.sameSide b AC) := by sorry

      -- greater than semicircle: center E inside the chord AC's arc side
      euclid_sentence "3.25.23"
        "And segment $ABC$ will manifestly be greater than a semi-circle."
        (step23 : b.sameSide e AC) := by sorry

      have hEb : |(e─a)| = |(e─b)| := by sorry
      have hEc : |(e─a)| = |(e─c)| := by sorry
      use α₃
      have haα₃ : a.onCircle α₃ := by sorry
      have hbα₃ : b.onCircle α₃ := by sorry
      have hcα₃ : c.onCircle α₃ := by sorry
      exact ⟨haα₃, hbα₃, hcα₃⟩

  euclid_conclude_sentence "3.25.24"
    "Thus, a circle has been completed from the given segment of a circle. (Which is) the very thing it was required to do."

end Elements.Book3
