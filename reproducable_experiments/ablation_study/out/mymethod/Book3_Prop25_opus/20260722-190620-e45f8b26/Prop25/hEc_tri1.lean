import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc_tri1 (a b c d e : Point) (AC AG3 DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB) (heDB : e.onLine DB)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (heoffac : ¬ e.onLine AC) :
    formTriangle d a e AC AG3 DB := by
  have hdAC : d.onLine AC := by euclid_finish
  have hdna : d ≠ a := by euclid_finish
  have hACneAG3 : AC ≠ AG3 := fun h => heoffac (h ▸ heAG3)
  have hDBneAC : DB ≠ AC := fun h => hboff (h ▸ hbDB)
  have haoffDB : ¬ a.onLine DB := by
    intro haDB
    euclid_apply (two_points_determine_line a d AC DB)
    euclid_finish
  have hAG3neDB : AG3 ≠ DB := fun h => haoffDB (h ▸ haAG3)
  euclid_finish

end Elements.Book3
