import SystemE
import Book3.Prop09.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (AC : Line) (α₁ : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (he_centre : e.isCentre α₁) (ha_circle : a.onCircle α₁)
    (hstep15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  -- The circle centred E with radius EA passes through B and C, since EB = EA = EC.
  euclid_apply (point_on_circle_if e a b α₁)
  euclid_apply (point_on_circle_if e a c α₁)
  -- E, equidistant from the three points A, B, C on the circle, is its centre [Prop.~3.9].
  euclid_apply (center_inside_circle e α₁)
  euclid_apply (Elements.Book3.proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
