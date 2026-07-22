import SystemE
import Book3.Prop09.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (AC : Line) (α₁ : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (he_ctr : e.isCentre α₁) (ha_on : a.onCircle α₁)
    (hab_e : |(a─e)| = |(b─e)|) (hbc_e : |(b─e)| = |(c─e)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  have hbon : b.onCircle α₁ := by euclid_finish
  have hcon : c.onCircle α₁ := by euclid_finish
  euclid_apply (center_inside_circle e α₁)
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
