import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step26
  (b c e : Point) (ABC : Circle)
  (hb_circ : b.onCircle ABC) (hc_circ : c.onCircle ABC) (hecenter : e.isCentre ABC)
  : |(e─c)| = |(e─b)| := by
  euclid_finish

end Elements.Book3
