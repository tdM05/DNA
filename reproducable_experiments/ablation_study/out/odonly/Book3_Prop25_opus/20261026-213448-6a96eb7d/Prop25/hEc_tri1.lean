import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc_tri1 (a b c d g3 e : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hg3a : g3 ≠ a) (hab_ne : a ≠ b) (hg3_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3) :
    formTriangle d a e AC AG3 DB := by
  have hgside : g3.sameSide d AB := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  euclid_apply (Elements.Book1.proposition_17 b a d AB AC DB)
  have hgoffAC : ¬ g3.onLine AC := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  euclid_finish

end Elements.Book3
