import SystemE
import Book3.Prop09.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (AC : Line) (α₁ : Circle)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬ b.onLine AC)
    (hcentre : e.isCentre α₁) (ha_circ : a.onCircle α₁)
    (hstep15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  -- B, C lie at the common radius from centre E, so they are on the circle.
  have hb : b.onCircle α₁ := by euclid_finish
  have hc : c.onCircle α₁ := by euclid_finish
  -- E is the centre of the completed circle through A, B, C [Prop.~3.9].
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
