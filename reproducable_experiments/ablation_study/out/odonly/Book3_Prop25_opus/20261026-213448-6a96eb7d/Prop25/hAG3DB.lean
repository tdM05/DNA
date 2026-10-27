import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hAG3DB (a b c d g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (habcb : |(a─b)| = |(c─b)|)
    (hbet : between a d c) (hadc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hab_ne : a ≠ b) (hg3_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) :
    AG3.intersectsLine DB := by
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have habd_lt : ∠ a:b:d < ∟ := by euclid_finish
  have hgside : g3.sameSide d AB := by euclid_finish
  euclid_apply (lines_intersect g3 a b d AG3 AB DB) as e'
  euclid_finish

end Elements.Book3
