import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step26
  (e c b : Point) (ABC : Circle)
  (hc : c.onCircle ABC) (hb : b.onCircle ABC)
  (step13 : e.isCentre ABC)
  : |(e─c)| = |(e─b)| := by
  euclid_finish

end Elements.Book3
