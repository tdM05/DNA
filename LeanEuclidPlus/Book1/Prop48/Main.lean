import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop11

namespace Elements.Book1

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ := by
  euclid_intros
  euclid_intro_sentence "1.48.0"
    "For let the square on one of the sides, $BC$, of triangle $ABC$ be equal to the (sum of the) squares on the sides $BA$ and $AC$. I say that angle $BAC$ is a right-angle. "

  euclid_apply (proposition_11'' a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  euclid_sentence "1.48.1"
    "For let $AD$ have been drawn from point $A$ at right-angles to the straight-line $AC$ [Prop.~1.11],"
    (step1 : ∠ d:a:c = ∟) := by sorry

  euclid_sentence "1.48.2"
    "and let $AD$ have been made equal to $BA$ [Prop.~1.3],"
    (step2 : |(a─d)| = |(b─a)|) := by sorry

  euclid_apply (line_from_points d c) as DC
  euclid_sentence "1.48.3"
    "and let $DC$ have been joined."
    (step3 : distinctPointsOnLine d c DC) := by sorry

  -- @assumption_valid
  have step4_assumption1 : |(d─a)| = |(a─b)| := by euclid_finish
  -- @assumption ("$DA$ is equal to $AB$", |(d─a)| = |(a─b)|)
  euclid_sentence "1.48.4"
    "Since $DA$ is equal to $AB$, the square on $DA$ is thus also equal to the square on $AB$."
    (step4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "1.48.5"
    "Let the square on $AC$ have been added to both."
    (step5 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)|) := by sorry

  euclid_sentence "1.48.6"
    "Thus, the (sum of the) squares on $DA$ and $AC$ is equal to the (sum of the) squares on $BA$ and $AC$."
    (step6 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by sorry

  -- @assumption_valid
  have step7_assumption1 : ∠ d:a:c = ∟ := by assumption
  -- @assumption ("angle $DAC$ is a right-angle", ∠ d:a:c = ∟)
  euclid_sentence "1.48.7"
    "But, the (square) on $DC$  is equal to the (sum of the squares) on $DA$ and $AC$. For angle $DAC$ is a right-angle [Prop.~1.47]."
    (step7 : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|) := by sorry

  -- @assumption_valid
  have step8_assumption1 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by assumption
  -- @assumption ("(that) was assumed", |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|)
  euclid_sentence "1.48.8"
    "But, the  (square) on $BC$ is equal to (sum of the squares) on $BA$ and $AC$. For (that) was assumed."
    (step8 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by sorry

  euclid_sentence "1.48.9"
    "Thus, the square on $DC$ is equal to the square on $BC$."
    (step9 : |(d─c)| * |(d─c)| = |(b─c)| * |(b─c)|) := by sorry

  euclid_sentence "1.48.10"
    "So  side $DC$ is also equal to (side) $BC$."
    (step10 : |(d─c)| = |(b─c)|) := by sorry

  -- @assumption_valid
  have step11_assumption1 : |(d─a)| = |(a─b)| := by assumption
  -- @assumption_valid
  have step11_assumption2 : distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$DA$ is equal to $AB$", |(d─a)| = |(a─b)|)
  -- @assumption ("$AC$ (is) common", distinctPointsOnLine a c AC)
  euclid_sentence "1.48.11"
    "And since $DA$ is equal to $AB$, and $AC$ (is) common, the two (straight-lines) $DA$, $AC$ are equal to the two (straight-lines) $BA$, $AC$."
    (step11 : |(d─a)| = |(b─a)| ∧ |(a─c)| = |(a─c)|) := by sorry

  euclid_sentence "1.48.12"
    "And the base $DC$ is equal to the base $BC$."
    (step12 : |(d─c)| = |(b─c)|) := by sorry

  euclid_sentence "1.48.13"
    "Thus, angle $DAC$ [is] equal to angle $BAC$ [Prop.~1.8]. "
    (step13 : ∠ d:a:c = ∠ b:a:c) := by sorry

  euclid_sentence "1.48.14"
    "But $DAC$ is a right-angle."
    (step14 : ∠ d:a:c = ∟) := by sorry

  euclid_sentence "1.48.15"
    "Thus, $BAC$ is also a right-angle. "
    (step15 : ∠ b:a:c = ∟) := by sorry

  exact step15
  euclid_conclude_sentence "1.48.16"
    "Thus, if the square on one of the sides of a triangle is equal to the (sum of the) squares on the remaining two sides of the triangle then the angle contained by the remaining two sides of the triangle is a right-angle. (Which is) the very thing it was required to show."

end Elements.Book1
