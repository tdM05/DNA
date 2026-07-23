import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri2 (a b c d e : Point) (AC EC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB) (heDB : e.onLine DB)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (heoffac : ¬ e.onLine AC) :
    formTriangle d c e AC EC DB := by
  -- d is on AC (between a and c) and distinct from c.
  have hdAC : d.onLine AC := by euclid_finish
  have hdnc : d ≠ c := by euclid_finish
  -- Line distinctnesses (cheap terms from off-line anchors).
  have hACneEC : AC ≠ EC := fun h => heoffac (h ▸ heEC)
  have hDBneAC : DB ≠ AC := fun h => hboff (h ▸ hbDB)
  -- c is off DB: else c,d ∈ AC∩DB with c≠d ⟹ AC = DB ⟹ b ∈ AC, contra.
  have hcoffDB : ¬ c.onLine DB := by
    intro hcDB
    euclid_apply (two_points_determine_line c d AC DB)
    euclid_finish
  have hECneDB : EC ≠ DB := fun h => hcoffDB (h ▸ hcEC)
  euclid_finish

end Elements.Book3
