import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9_assumption1 (a b d e : Point) (AB DB : Line)
    (hbde : between b d e) (hab : a ≠ b) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB) (heDB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d) : ∠ a:b:e = ∠ b:a:e := by
  -- d between b and e ⟹ ray b→d = ray b→e, so ∠a:b:d = ∠a:b:e (ray extension); with step6 done.
  euclid_apply (equal_angles b a a d e AB DB)
  euclid_finish

end Elements.Book3
