import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step17 (a b c d e : Point) (AC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (hbde : between b d e) : e.opposingSides b AC := by
  -- d = AC ∩ DB lies between b and e, so b and e are on opposite sides of AC.
  have hdAC : d.onLine AC := by euclid_finish
  have heAC : ¬ e.onLine AC := by
    intro hcon
    euclid_apply (two_points_determine_line d e DB AC)
    euclid_finish
  euclid_apply (pasch_3 b d e AC)
  euclid_finish

end Elements.Book3
