import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step14
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbdca : between d c a)
  (hfDA : f.onLine DA)
  (hang : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (hcentre : e.isCentre ABC)
  (hnotthrough : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
  : f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  euclid_finish

end Elements.Book3
