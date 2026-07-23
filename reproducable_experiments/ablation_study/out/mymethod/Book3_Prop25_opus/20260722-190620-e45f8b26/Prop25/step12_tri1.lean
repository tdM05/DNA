import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri1 (a b c d e : Point) (AC AG DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB) (heDB : e.onLine DB)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (heoffac : ¬ e.onLine AC) :
    formTriangle d a e AC AG DB := by
  -- d is on AC (it is between a and c, both on AC), and distinct from a.
  have hdAC : d.onLine AC := by euclid_finish
  have hdna : d ≠ a := by euclid_finish
  -- Line distinctnesses (cheap terms from off-line anchors).
  have hACneAG : AC ≠ AG := fun h => heoffac (h ▸ heAG)
  have hDBneAC : DB ≠ AC := fun h => hboff (h ▸ hbDB)
  -- a is off DB: else a,d ∈ AC∩DB with a≠d ⟹ AC = DB ⟹ b ∈ AC, contra.
  have haoffDB : ¬ a.onLine DB := by
    intro haDB
    euclid_apply (two_points_determine_line a d AC DB)
    euclid_finish
  have hAGneDB : AG ≠ DB := fun h => haoffDB (h ▸ haAG)
  euclid_finish

end Elements.Book3
