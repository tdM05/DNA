import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hassump1 : ∠ a:b:d = ∠ b:a:d)
    (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|) :
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  euclid_apply (Elements.Book1.proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
