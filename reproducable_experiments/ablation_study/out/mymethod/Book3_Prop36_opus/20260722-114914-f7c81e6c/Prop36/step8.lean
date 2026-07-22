import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8
  (a b c d f : Point) (ABC : Circle) (FB DA DB : Line)
  (hfFB : f.onLine FB) (hbFB : b.onLine FB)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC) (hb : b.onCircle ABC)
  (hfcentre : f.isCentre ABC) (hbdca : between d c a)
  (hnint : ¬ DB.intersectsCircle ABC)
  (step3 : ∠ f:b:d = ∟)
  : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_apply (Elements.Book1.proposition_47 b f d FB DA DB)
  euclid_finish

end Elements.Book3
