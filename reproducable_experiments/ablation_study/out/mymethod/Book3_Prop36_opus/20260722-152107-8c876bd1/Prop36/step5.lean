import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step5 (a c d f : Point) (ABC : Circle) (DA : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC) (hf_centre : f.isCentre ABC)
  (hbtw : between d c a) (hbisect : |(a─f)| = |(f─c)|)
  : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hac : distinctPointsOnLine a c DA := by euclid_finish
  have hafc : between a f c := by euclid_finish
  have hacd : between a c d := by euclid_finish
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
