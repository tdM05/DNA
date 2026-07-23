import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step8 (e c : Point) (EC : Line)
    (heEC : e.onLine EC) (hcEC : c.onLine EC) (hec : e ≠ c) :
    distinctPointsOnLine e c EC := by
  euclid_finish

end Elements.Book3
