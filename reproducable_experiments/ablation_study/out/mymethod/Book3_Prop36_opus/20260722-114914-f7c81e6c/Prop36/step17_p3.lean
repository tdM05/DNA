import SystemE
import Book3.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_p3
  (a c e f : Point) (ABC : Circle) (DA EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hcDA : c.onLine DA) (hfDA : f.onLine DA)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (hcentre : e.isCentre ABC) (hnotDA : ¬ e.onLine DA)
  (hafe : ∠ a:f:e = ∟)
  (hac : a ≠ c)
  (hbet : between a f c)
  : |(a─f)| = |(f─c)| := by
  euclid_apply (proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3
