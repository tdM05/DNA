import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20
  (a c d f : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbet_dca : between d c a)
  (step17 : |(a─f)| = |(f─c)|)
  : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
