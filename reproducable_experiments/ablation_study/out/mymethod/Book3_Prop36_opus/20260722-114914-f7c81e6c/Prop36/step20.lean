import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20
  (a c d f : Point) (ABC : Circle) (DA : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbdca : between d c a)
  (step19 : |(a─f)| = |(f─c)|)
  : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hac : distinctPointsOnLine a c DA := by euclid_finish
  have hafc : between a f c := by euclid_finish
  have hacd : between a c d := by euclid_finish
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
