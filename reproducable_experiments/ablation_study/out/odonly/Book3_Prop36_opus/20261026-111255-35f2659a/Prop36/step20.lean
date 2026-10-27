import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20 (a c d f : Point) (ABC : Circle) (DA : Line)
  (haC : a.onCircle ABC) (hcC : c.onCircle ABC)
  (hdca : between d c a) (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hfDA : f.onLine DA)
  (hhalf : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA (by euclid_finish))
  euclid_finish

end Elements.Book3
