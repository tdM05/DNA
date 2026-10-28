import SystemE
import Book1.Prop10.Main
import Book1.Prop23.Main
import Book3.Prop25.step1
import Book3.Prop25.step2
import Book3.Prop25.step3
import Book3.Prop25.step4
import Book3.Prop25.step5
import Book3.Prop25.step6
import Book3.Prop25.step7
import Book3.Prop25.step8
import Book3.Prop25.step9
import Book3.Prop25.step10
import Book3.Prop25.step11
import Book3.Prop25.step12
import Book3.Prop25.step13
import Book3.Prop25.step14
import Book3.Prop25.step15
import Book3.Prop25.step16
import Book3.Prop25.step17
import Book3.Prop25.step18
import Book3.Prop25.step19
import Book3.Prop25.step20
import Book3.Prop25.step21
import Book3.Prop25.step22
import Book3.Prop25.hgap1
import Book3.Prop25.hint1
import Book3.Prop25.step9_assumption1
import Book3.Prop25.hca2
import Book3.Prop25.hcb2
import Book3.Prop25.hcc2
import Book3.Prop25.hgap3
import Book3.Prop25.hint3
import Book3.Prop25.step21_assumption2
import Book3.Prop25.hca3
import Book3.Prop25.hcb3
import Book3.Prop25.hcc3
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

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
    (step1 : |(a─d)| = |(d─c)|) := by euclid_apply (helper_3_25_step1 a d c (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)))

  -- Draw the perpendicular DB from D (the line through D and the given arc-point B).
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.25.2"
    "and let $DB$ be drawn from point $D$, at right-angles to $AC$ [Prop.~1.11]."
    (step2 : ∠ a:d:b = ∟) := by euclid_apply (helper_3_25_step2 a b c d AC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show |(a─b)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)))

  -- Join AB.
  euclid_apply (line_from_points a b) as AB
  euclid_sentence "3.25.3"
    "And let $AB$ be joined."
    (step3 : distinctPointsOnLine a b AB) := by euclid_apply (helper_3_25_step3 a b AC AB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))

  euclid_sentence "3.25.4"
    "Thus, angle $ABD$ is surely either greater than, equal to, or less than (angle) $BAD$."
    (step4 : ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d) := by euclid_apply (helper_3_25_step4 a b d)

  rcases step4 with hgt | heq | hlt
  ·
    -- CASE 1: angle ABD greater than angle BAD.
    euclid_sentence "3.25.5"
      "First of all, let it be greater."
      (step5 : ∠ a:b:d > ∠ b:a:d) := by euclid_apply (helper_3_25_step5 a b d (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))

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
    have hgap1 : e0p ≠ a ∧ ∠ e0p:a:b = ∠ a:b:d ∧ e0p.sameSide d AB := by euclid_apply (helper_3_25_hgap1 a b d e0p bImg AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∠ bImg:a:e0p; assumption)) (by euclid_assumption "" (show |(b─a)| = |(a─bImg)|; assumption)) (by euclid_assumption "" (show bImg.onLine AB; assumption)) (by euclid_assumption "" (show ¬between bImg a b; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a ≠ e0p; assumption)))
    obtain ⟨he0p_ne, he0p_ang, he0p_side⟩ := hgap1
    euclid_apply (line_from_points a e0p) as AE
    have hint1 : AE.intersectsLine DB := by euclid_apply (helper_3_25_hint1 a b c d e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)))
    euclid_apply (intersection_lines AE DB) as e
    euclid_sentence "3.25.6"
      "And let (angle) $BAE$, equal to angle $ABD$, be constructed on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]."
      (step6 : ∠ b:a:e = ∠ a:b:d) := by euclid_apply (helper_3_25_step6 a b c d e e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)))

    euclid_sentence "3.25.7"
      "And let $DB$ be drawn through to $E$,"
      (step7 : between b d e) := by euclid_apply (helper_3_25_step7 a b c d e e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)))

    euclid_apply (line_from_points e c) as EC
    euclid_sentence "3.25.8"
      "and let $EC$ be joined."
      (step8 : distinctPointsOnLine e c EC) := by euclid_apply (helper_3_25_step8 a b c d e AC DB EC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)))

    -- @assumption_gap
    have step9_assumption1 : ∠ a:b:e = ∠ b:a:e := by euclid_apply (helper_3_25_step9_assumption1 a b d e AB DB (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)))
    -- @assumption ("angle $ABE$ is equal to $BAE$", ∠ a:b:e = ∠ b:a:e)
    euclid_sentence "3.25.9"
      "Therefore, since angle $ABE$ is equal to $BAE$, the straight-line $EB$ is thus also equal to $EA$ [Prop.~1.6]."
      (step9 : |(e─b)| = |(e─a)|) := by euclid_apply (helper_3_25_step9 a b c d e e0p AC AE AB DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "angle $ABE$ is equal to $BAE$" (show ∠ a:b:e = ∠ b:a:e; assumption)))

    -- @assumption_valid
    have step10_assumption1 : |(a─d)| = |(d─c)| := by assumption
    -- @assumption_valid
    have step10_assumption2 : |(d─e)| = |(d─e)| := by rfl
    -- @assumption ("$AD$ is equal to $DC$", |(a─d)| = |(d─c)|)
    -- @assumption ("$DE$ (is) common", |(d─e)| = |(d─e)|)
    euclid_sentence "3.25.10"
      "And since $AD$ is equal to $DC$, and $DE$ (is) common, the two (straight-lines) $AD$, $DE$ are equal to the two (straight-lines) $CD$, $DE$, respectively."
      (step10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) := by euclid_apply (helper_3_25_step10 a c d e (by euclid_assumption "$AD$ is equal to $DC$" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "$DE$ (is) common" (show |(d─e)| = |(d─e)|; assumption)))

    -- @assumption_valid
    have step11_assumption1 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟ := by euclid_finish
    -- @assumption ("each (is) a right-angle", ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    euclid_sentence "3.25.11"
      "And angle $ADE$ is equal to angle $CDE$. For each (is) a right-angle."
      (step11 : ∠ a:d:e = ∠ c:d:e) := by euclid_apply (helper_3_25_step11 a c d e (by euclid_assumption "each (is) a right-angle" (show ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟; assumption)))

    euclid_sentence "3.25.12"
      "Thus, the base $AE$ is equal to the base $CE$ [Prop.~1.4]."
      (step12 : |(a─e)| = |(c─e)|) := by euclid_apply (helper_3_25_step12 a b c d e AC AE DB EC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∠ c:d:e; assumption)))

    -- @assumption_valid
    have step13_assumption1 : |(a─e)| = |(b─e)| := by euclid_finish
    -- @assumption ("$AE$ was shown (to be) equal to $BE$", |(a─e)| = |(b─e)|)
    euclid_sentence "3.25.13"
      "But, $AE$ was shown (to be) equal to $BE$. Thus, $BE$ is also equal to $CE$."
      (step13 : |(b─e)| = |(c─e)|) := by euclid_apply (helper_3_25_step13 a b c e (by euclid_assumption "" (show |(a─e)| = |(c─e)|; assumption)) (by euclid_assumption "$AE$ was shown (to be) equal to $BE$" (show |(a─e)| = |(b─e)|; assumption)))

    euclid_sentence "3.25.14"
      "Thus, the three (straight-lines) $AE$, $EB$, and $EC$ are equal to one another."
      (step14 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) := by euclid_apply (helper_3_25_step14 a b c e (by euclid_assumption "" (show |(e─b)| = |(e─a)|; assumption)) (by euclid_assumption "" (show |(a─e)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─e)|; assumption)))

    -- The completed circle: centre E, radius EA (so A is on it); B and C are the remaining points.
    euclid_apply (circle_from_points e a) as α
    euclid_sentence "3.25.15"
      "Thus, if a circle is drawn with center $E$, and radius one of $AE$, $EB$, or $EC$, it will also go through the remaining points (of the segment), and the (associated circle) will be completed [Prop.~3.9]."
      (step15 : b.onCircle α ∧ c.onCircle α) := by euclid_apply (helper_3_25_step15 a b c e AC α (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show e.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─c)|; assumption)))

    euclid_sentence "3.25.16"
      "Thus, a circle has been completed from the given segment of a circle."
      (step16 : a.onCircle α ∧ b.onCircle α ∧ c.onCircle α) := by euclid_apply (helper_3_25_step16 a b c α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α ∧ c.onCircle α; assumption)))

    -- "less than a semi-circle" ⟺ the centre E lies outside the segment, i.e. on the opposite
    -- side of the chord AC from the arc-point B.
    euclid_sentence "3.25.17"
      "And (it is) clear that the segment $ABC$ is less than a semi-circle, because the center $E$ happens to lie outside it."
      (step17 : e.opposingSides b AC) := by euclid_apply (helper_3_25_step17 a b c d e AC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show between b d e; assumption)))

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
      (step18 : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)|) := by euclid_apply (helper_3_25_step18 a b c d AC AB DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "angle $ABD$ is equal to $BAD$" (show ∠ a:b:d = ∠ b:a:d; assumption)) (by euclid_assumption "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$" (show |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|; assumption)))

    -- The completed circle in this case: centre D, radius DA.
    euclid_apply (circle_from_points d a) as α
    euclid_sentence "3.25.19"
      "And point $D$ will be the center of the completed circle."
      (step19 : d.isCentre α) := by euclid_apply (helper_3_25_step19 d α (by euclid_assumption "" (show d.isCentre α; assumption)))

    -- "a semi-circle" ⟺ the centre D lies on the chord AC (so AC is a diameter).
    euclid_sentence "3.25.20"
      "And $ABC$ will manifestly be a semi-circle."
      (step20 : d.onLine AC) := by euclid_apply (helper_3_25_step20 a c d AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)))

    have hca2 : a.onCircle α := by euclid_apply (helper_3_25_hca2 a α (by euclid_assumption "" (show a.onCircle α; assumption)))
    have hcb2 : b.onCircle α := by euclid_apply (helper_3_25_hcb2 a b d α (by euclid_assumption "" (show d.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))
    have hcc2 : c.onCircle α := by euclid_apply (helper_3_25_hcc2 a c d α (by euclid_assumption "" (show d.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)))
    exact ⟨α, hca2, hcb2, hcc2⟩

  ·
    -- CASE 3: angle ABD less than angle BAD.
    -- Reconstruct E as in case 1 (ray from A with angle BAE = ABD, met with the perpendicular DB).
    euclid_apply (proposition_23 a b b a d AB AB DB) as e0
    -- @euclid_gap: exactly as in case 1 — proposition_23 fixes only the magnitude ∠e0:a:b = ∠a:b:d, not
    --   the side of AB. Euclid's I.23 builds it on d's side so ray AE meets DB; the formal statement
    --   drops that. Recover the implicit side via a superposition copy e0p of the ray on d's side.
    euclid_apply (superposition b a d a b d AB AC DB AB) as (bImg, e0p, BCimg, ACimg)
    have hgap3 : e0p ≠ a ∧ ∠ e0p:a:b = ∠ a:b:d ∧ e0p.sameSide d AB := by euclid_apply (helper_3_25_hgap3 a b d e0p bImg AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∠ bImg:a:e0p; assumption)) (by euclid_assumption "" (show |(b─a)| = |(a─bImg)|; assumption)) (by euclid_assumption "" (show bImg.onLine AB; assumption)) (by euclid_assumption "" (show ¬between bImg a b; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a ≠ e0p; assumption)))
    obtain ⟨he0p_ne3, he0p_ang3, he0p_side3⟩ := hgap3
    euclid_apply (line_from_points a e0p) as AE
    have hint3 : AE.intersectsLine DB := by euclid_apply (helper_3_25_hint3 a b c d e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)))
    euclid_apply (intersection_lines AE DB) as e
    -- @assumption_valid
    have step21_assumption1 : ∠ a:b:d < ∠ b:a:d := by assumption
    -- @assumption_gap
    have step21_assumption2 : ∠ b:a:e = ∠ a:b:d := by euclid_apply (helper_3_25_step21_assumption2 a b c d e e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)))
    -- @assumption ("$ABD$ is less than $BAD$", ∠ a:b:d < ∠ b:a:d)
    -- @assumption ("we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]", ∠ b:a:e = ∠ a:b:d)
    euclid_sentence "3.25.21"
      "And if $ABD$ is less than $BAD$, and we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23], then the center will fall on $DB$, inside the segment $ABC$."
      (step21 : e.onLine DB) := by euclid_apply (helper_3_25_step21 a b d e DB (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "$ABD$ is less than $BAD$" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]" (show ∠ b:a:e = ∠ a:b:d; assumption)))

    -- "greater than a semi-circle" ⟺ the centre E lies inside the segment, i.e. on the same
    -- side of the chord AC as the arc-point B.
    euclid_sentence "3.25.22"
      "And segment $ABC$ will manifestly be greater than a semi-circle."
      (step22 : e.sameSide b AC) := by euclid_apply (helper_3_25_step22 a b c d e e0p AC DB AB AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)))

    euclid_apply (circle_from_points e a) as α
    have hca3 : a.onCircle α := by euclid_apply (helper_3_25_hca3 a α (by euclid_assumption "" (show a.onCircle α; assumption)))
    have hcb3 : b.onCircle α := by euclid_apply (helper_3_25_hcb3 a b c d e e0p AC DB AB AE α (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0p:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show e0p.sameSide d AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0p.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)))
    have hcc3 : c.onCircle α := by euclid_apply (helper_3_25_hcc3 a b c d e AC DB AE α (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "" (show e.sameSide b AC; assumption)) (by euclid_assumption "" (show e.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)))
    exact ⟨α, hca3, hcb3, hcc3⟩

  euclid_conclude_sentence "3.25.23"
    "Thus, a circle has been completed from the given segment of a circle. (Which is) the very thing it was required to do."

end Elements.Book3
