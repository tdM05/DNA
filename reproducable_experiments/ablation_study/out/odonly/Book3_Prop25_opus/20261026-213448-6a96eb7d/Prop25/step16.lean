import SystemE
import Book3.Prop09.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (AC : Line) (α₁ : Circle)
    (hcen : e.isCentre α₁) (haC : a.onCircle α₁)
    (hac : a ≠ c) (hab_ne : a ≠ b)
    (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hstep15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  have hb : b.onCircle α₁ := by euclid_finish
  have hc : c.onCircle α₁ := by euclid_finish
  euclid_apply (Elements.Book3.proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
