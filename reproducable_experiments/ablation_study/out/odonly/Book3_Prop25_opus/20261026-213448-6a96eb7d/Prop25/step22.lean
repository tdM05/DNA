import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step22 (a b c d g3 e : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hg3a : g3 ≠ a) (hab_ne : a ≠ b) (hg3_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3) :
    e.onLine DB ∧ e.sameSide b AC := by
  refine ⟨heDB, ?_⟩
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hg3side : g3.sameSide d AB := by euclid_finish
  have hg3b : g3.sameSide b AC := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 b a d AB AC DB)
  have hbad_lt : ∠ b:a:d < ∟ := by euclid_finish
  have hg3ad : ∠ g3:a:d < ∟ := by euclid_finish
  euclid_apply (lines_intersect g3 a d b AG3 AC DB) as e''
  euclid_finish

end Elements.Book3
