import SystemE
import Book1.Prop06.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step9 (a b c d e : Point) (AC DB AB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ a:b:e = ∠ b:a:e)   -- "angle $ABE$ is equal to $BAE$"
    : |(e─b)| = |(e─a)| := by
  -- Triangle ABE has ∠BAE = ∠ABE ⟹ EA = EB [Prop.~1.6].
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_6 e a b EA AB EB)
  euclid_finish

end Elements.Book3
