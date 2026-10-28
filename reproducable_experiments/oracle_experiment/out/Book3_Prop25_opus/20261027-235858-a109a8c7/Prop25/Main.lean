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

  -- Cut AC in half at D [I.10]: D is the midpoint of AC.
  euclid_apply (proposition_10 a c AC) as d
  euclid_sentence "3.25.1"
    "For let $AC$ be cut in half at (point) $D$ [Prop.~1.10],"
    (step1 : |(a─d)| = |(d─c)|) := by sorry

  -- Draw the perpendicular DB from D (the line through D and the given arc-point B).
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.25.2"
    "and let $DB$ be drawn from point $D$, at right-angles to $AC$ [Prop.~1.11]."
    (step2 : ∠ a:d:b = ∟) := by sorry

  -- Join AB.
  euclid_apply (line_from_points a b) as AB
  euclid_sentence "3.25.3"
    "And let $AB$ be joined."
    (step3 : distinctPointsOnLine a b AB) := by sorry

  euclid_sentence "3.25.4"
    "Thus, angle $ABD$ is surely either greater than, equal to, or less than (angle) $BAD$."
    (step4 : ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d) := by sorry

  rcases step4 with hgt | heq | hlt
  ·
    -- CASE 1: angle ABD greater than angle BAD.
    euclid_sentence "3.25.5"
      "First of all, let it be greater."
      (step5 : ∠ a:b:d > ∠ b:a:d) := by sorry

    -- Construct E: the ray from A making angle BAE = ABD (on line BA at A) [I.23],
    -- extended to meet the perpendicular DB.
    euclid_apply (proposition_23 a b b a d AB AB DB) as e0
    -- @euclid_gap: proposition_23 fixes only the MAGNITUDE ∠e0:a:b = ∠a:b:d, not the SIDE of AB the
    --   equal angle opens toward. Euclid's I.23 constructs it on d's side (so ray AE meets the
    --   perpendicular DB); the formalized statement drops that side, and the far-side witness gives
    --   equal ALTERNATE angles ⟹ AE ∥ DB with no meet (oracle-confirmed gap). Recover the implicit
    --   side: superposition copies △bad onto line BA fixing A, placing the image e0p of d on d's
    --   side of AB — an equal-angle ray ∠e0p:a:b = ∠a:b:d guaranteed on the correct side.
    euclid_apply (superposition b a d a b d AB AC DB AB) as (bImg, e0p, BCimg, ACimg)
    have hgap1 : e0p ≠ a ∧ ∠ e0p:a:b = ∠ a:b:d ∧ e0p.sameSide d AB := by sorry
    obtain ⟨he0p_ne, he0p_ang, he0p_side⟩ := hgap1
    euclid_apply (line_from_points a e0p) as AE
    have hint1 : AE.intersectsLine DB := by sorry
    euclid_apply (intersection_lines AE DB) as e
    euclid_sentence "3.25.6"
      "And let (angle) $BAE$, equal to angle $ABD$, be constructed on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]."
      (step6 : ∠ b:a:e = ∠ a:b:d) := by sorry

    euclid_sentence "3.25.7"
      "And let $DB$ be drawn through to $E$,"
      (step7 : between b d e) := by sorry

    euclid_apply (line_from_points e c) as EC
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
    -- @assumption ("each (is) a right-angle", ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    euclid_sentence "3.25.11"
      "And angle $ADE$ is equal to angle $CDE$. For each (is) a right-angle."
      (step11 : ∠ a:d:e = ∠ c:d:e) := by sorry

    euclid_sentence "3.25.12"
      "Thus, the base $AE$ is equal to the base $CE$ [Prop.~1.4]."
      (step12 : |(a─e)| = |(c─e)|) := by sorry

    -- @assumption_valid
    have step13_assumption1 : |(a─e)| = |(b─e)| := by euclid_finish
    -- @assumption ("$AE$ was shown (to be) equal to $BE$", |(a─e)| = |(b─e)|)
    euclid_sentence "3.25.13"
      "But, $AE$ was shown (to be) equal to $BE$. Thus, $BE$ is also equal to $CE$."
      (step13 : |(b─e)| = |(c─e)|) := by sorry

    euclid_sentence "3.25.14"
      "Thus, the three (straight-lines) $AE$, $EB$, and $EC$ are equal to one another."
      (step14 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) := by sorry

    -- The completed circle: centre E, radius EA (so A is on it); B and C are the remaining points.
    euclid_apply (circle_from_points e a) as α
    euclid_sentence "3.25.15"
      "Thus, if a circle is drawn with center $E$, and radius one of $AE$, $EB$, or $EC$, it will also go through the remaining points (of the segment), and the (associated circle) will be completed [Prop.~3.9]."
      (step15 : b.onCircle α ∧ c.onCircle α) := by sorry

    euclid_sentence "3.25.16"
      "Thus, a circle has been completed from the given segment of a circle."
      (step16 : a.onCircle α ∧ b.onCircle α ∧ c.onCircle α) := by sorry

    -- "less than a semi-circle" ⟺ the centre E lies outside the segment, i.e. on the opposite
    -- side of the chord AC from the arc-point B.
    euclid_sentence "3.25.17"
      "And (it is) clear that the segment $ABC$ is less than a semi-circle, because the center $E$ happens to lie outside it."
      (step17 : e.opposingSides b AC) := by sorry

    exact ⟨α, step16⟩

  ·
    -- CASE 2: angle ABD equal to angle BAD.
    -- @assumption_valid
    have step18_assumption1 : ∠ a:b:d = ∠ b:a:d := by assumption
    -- @assumption_valid
    have step18_assumption2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)| := by euclid_finish
    -- @assumption ("angle $ABD$ is equal to $BAD$", ∠ a:b:d = ∠ b:a:d)
    -- @assumption ("$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$", |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
    euclid_sentence "3.25.18"
      "[And], similarly, even if angle $ABD$ is equal to $BAD$, (since) $AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$, the three (straight-lines) $DA$, $DB$, and $DC$ will be equal to one another."
      (step18 : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)|) := by sorry

    -- The completed circle in this case: centre D, radius DA.
    euclid_apply (circle_from_points d a) as α
    euclid_sentence "3.25.19"
      "And point $D$ will be the center of the completed circle."
      (step19 : d.isCentre α) := by sorry

    -- "a semi-circle" ⟺ the centre D lies on the chord AC (so AC is a diameter).
    euclid_sentence "3.25.20"
      "And $ABC$ will manifestly be a semi-circle."
      (step20 : d.onLine AC) := by sorry

    have hca2 : a.onCircle α := by sorry
    have hcb2 : b.onCircle α := by sorry
    have hcc2 : c.onCircle α := by sorry
    exact ⟨α, hca2, hcb2, hcc2⟩

  ·
    -- CASE 3: angle ABD less than angle BAD.
    -- Reconstruct E as in case 1 (ray from A with angle BAE = ABD, met with the perpendicular DB).
    euclid_apply (proposition_23 a b b a d AB AB DB) as e0
    -- @euclid_gap: exactly as in case 1 — proposition_23 fixes only the magnitude ∠e0:a:b = ∠a:b:d, not
    --   the side of AB. Euclid's I.23 builds it on d's side so ray AE meets DB; the formal statement
    --   drops that. Recover the implicit side via a superposition copy e0p of the ray on d's side.
    euclid_apply (superposition b a d a b d AB AC DB AB) as (bImg, e0p, BCimg, ACimg)
    have hgap3 : e0p ≠ a ∧ ∠ e0p:a:b = ∠ a:b:d ∧ e0p.sameSide d AB := by sorry
    obtain ⟨he0p_ne3, he0p_ang3, he0p_side3⟩ := hgap3
    euclid_apply (line_from_points a e0p) as AE
    have hint3 : AE.intersectsLine DB := by sorry
    euclid_apply (intersection_lines AE DB) as e
    -- @assumption_valid
    have step21_assumption1 : ∠ a:b:d < ∠ b:a:d := by assumption
    -- @assumption_gap
    have step21_assumption2 : ∠ b:a:e = ∠ a:b:d := by sorry
    -- @assumption ("$ABD$ is less than $BAD$", ∠ a:b:d < ∠ b:a:d)
    -- @assumption ("we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]", ∠ b:a:e = ∠ a:b:d)
    euclid_sentence "3.25.21"
      "And if $ABD$ is less than $BAD$, and we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23], then the center will fall on $DB$, inside the segment $ABC$."
      (step21 : e.onLine DB) := by sorry

    -- "greater than a semi-circle" ⟺ the centre E lies inside the segment, i.e. on the same
    -- side of the chord AC as the arc-point B.
    euclid_sentence "3.25.22"
      "And segment $ABC$ will manifestly be greater than a semi-circle."
      (step22 : e.sameSide b AC) := by sorry

    euclid_apply (circle_from_points e a) as α
    have hca3 : a.onCircle α := by sorry
    have hcb3 : b.onCircle α := by sorry
    have hcc3 : c.onCircle α := by sorry
    exact ⟨α, hca3, hcb3, hcc3⟩

  euclid_conclude_sentence "3.25.23"
    "Thus, a circle has been completed from the given segment of a circle. (Which is) the very thing it was required to do."

end Elements.Book3
