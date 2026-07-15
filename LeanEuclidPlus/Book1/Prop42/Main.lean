import SystemE
import Book1.Prop10.Main
import Book1Variants.Prop23
import Book1.Prop31.Main
import Book1.Prop38.Main
import Book1.Prop41.Main

namespace Elements.Book1

theorem proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) := by
  euclid_intros
  euclid_intro_sentence "1.42.0"
    "To construct a parallelogram equal to a given triangle in a given rectilinear angle. Let $ABC$ be the given triangle, and $D$ the given rectilinear angle. So it is required to construct a parallelogram equal to triangle $ABC$ in the rectilinear angle $D$."

  euclid_apply (proposition_10 b c BC) as e
  euclid_sentence "1.42.1"
    "Let $BC$ have been cut in half at $E$ [Prop.~1.10],"
    (step1 : between b e c ∧ |(b─e)| = |(e─c)|) := by sorry

  euclid_apply (line_from_points a e) as AE
  euclid_sentence "1.42.2"
    "and let $AE$ have been joined."
    (step2 : distinctPointsOnLine a e AE) := by sorry

  euclid_apply (proposition_23' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as f₀
  euclid_apply (line_from_points e f₀) as EF
  euclid_sentence "1.42.3"
    "And let (angle) $CEF$, equal to angle $D$,  have been constructed at the point $E$ on the straight-line $EC$ [Prop.~1.23]."
    (step3 : ∠ c:e:f₀ = ∠ d₁:d₂:d₃) := by sorry

  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_sentence "1.42.4"
    "And let $AG$ have been drawn through $A$ parallel to $EC$ [Prop.~1.31],"
    (step4 : a.onLine AG ∧ ¬(AG.intersectsLine BC)) := by sorry

  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_sentence "1.42.5"
    "and let $CG$ have been drawn through $C$ parallel to $EF$ [Prop.~1.31]."
    (step5 : c.onLine CG ∧ ¬(CG.intersectsLine EF)) := by sorry

  euclid_sentence "1.42.6"
    "Thus, $FECG$ is a parallelogram."
    (step6 : formParallelogram f g e c AG BC EF CG) := by sorry

  -- @assumption_valid
  have step7_assumption1 : |(b─e)| = |(e─c)| := by assumption
  -- @assumption_valid
  have step7_assumption2 : |(b─e)| = |(e─c)| := by assumption
  -- @assumption_valid
  have step7_assumption3 : ¬(AG.intersectsLine BC) := by assumption
  -- @assumption ("$BE$ is equal to $EC$", |(b─e)| = |(e─c)|)
  -- @assumption ("the equal bases, $BE$ and $EC$", |(b─e)| = |(e─c)|)
  -- @assumption ("the same parallels, $BC$ and $AG$", ¬(AG.intersectsLine BC))
  euclid_sentence "1.42.7"
    "And since $BE$ is equal to $EC$, triangle $ABE$ is also equal to triangle $AEC$. For they are on the equal bases, $BE$ and $EC$, and between the same parallels, $BC$ and $AG$ [Prop.~1.38]."
    (step7 : Triangle.area △ a:b:e = Triangle.area △ a:e:c) := by sorry

  euclid_sentence "1.42.8"
    "Thus, triangle $ABC$ is double (the area) of triangle $AEC$."
    (step8 : Triangle.area △ a:b:c = Triangle.area △ a:e:c + Triangle.area △ a:e:c) := by sorry

  -- @assumption_valid
  have step9_assumption1 : distinctPointsOnLine e c BC := by euclid_finish
  -- @assumption_valid
  have step9_assumption2 : ¬(AG.intersectsLine BC) := by assumption
  -- @assumption ("the same base as ($AEC$)", distinctPointsOnLine e c BC)
  -- @assumption ("the same parallels  as ($AEC$)", ¬(AG.intersectsLine BC))
  euclid_sentence "1.42.9"
    "And parallelogram $FECG$ is also double (the area) of triangle $AEC$. For it has the same base as ($AEC$), and is between the same parallels  as ($AEC$) [Prop.~1.41]."
    (step9 : Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:e:c + Triangle.area △ a:e:c) := by sorry

  euclid_sentence "1.42.10"
    "Thus, parallelogram $FECG$ is equal to triangle $ABC$. "
    (step10 : Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:b:c) := by sorry

  euclid_sentence "1.42.11"
    "($FECG$) also has the angle $CEF$ equal to the given (angle) $D$."
    (step11 : ∠ c:e:f = ∠ d₁:d₂:d₃) := by sorry

  use f, g, e, c, AG, BC, EF, CG
  euclid_conclude_sentence "1.42.12"
    "Thus, parallelogram $FECG$,  equal to the given triangle $ABC$, has been constructed in the angle $CEF$, which is equal to $D$. (Which is) the very thing it was required to do."

end Elements.Book1
