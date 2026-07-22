import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step6
  (f c b : Point) (ABC : Circle)
  (hc : c.onCircle ABC) (hb : b.onCircle ABC) (hfcentre : f.isCentre ABC)
  : |(f─c)| = |(f─b)| := by
  euclid_finish

end Elements.Book3
