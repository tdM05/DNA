import SystemE
import Book3.Prop09.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (α₁ : Circle) (AC : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c) (hb_off : ¬b.onLine AC)
    (he_centre : e.isCentre α₁) (ha_circ : a.onCircle α₁)
    (hstep15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  obtain ⟨h1, h2⟩ := hstep15
  -- B and C are equidistant from the centre E, so they lie on the circle
  have hb_circ : b.onCircle α₁ := by euclid_finish
  have hc_circ : c.onCircle α₁ := by euclid_finish
  -- E, with three equal radii EA, EB, EC, is the centre of the completed circle [Prop.~3.9]
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
