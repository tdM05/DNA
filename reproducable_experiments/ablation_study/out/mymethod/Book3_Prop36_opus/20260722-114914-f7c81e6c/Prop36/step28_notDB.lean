import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28_notDB
  (e : Point) (ABC : Circle) (DB : Line)
  (step13 : e.isCentre ABC)
  (hnint : ¬ DB.intersectsCircle ABC)
  : ¬ e.onLine DB := by euclid_finish

end Elements.Book3
