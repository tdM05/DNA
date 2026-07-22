import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
    (h_aABC : a.onCircle ABC) (h_fc : f.isCentre ABC)
    (h_aADE : a.onCircle ADE) (h_gc : g.isCentre ADE)
    (h_aAF : a.onLine AF) (h_fAF : f.onLine AF)
    (h_aAG : a.onLine AG) (h_gAG : g.onLine AG) :
    distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3
