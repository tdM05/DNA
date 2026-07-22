import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step22 (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hg3side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3)
    (hassump1 : ∠ a:b:d < ∠ b:a:d) :
    e.onLine DB ∧ e.sameSide b AC := by
  euclid_finish

end Elements.Book3
