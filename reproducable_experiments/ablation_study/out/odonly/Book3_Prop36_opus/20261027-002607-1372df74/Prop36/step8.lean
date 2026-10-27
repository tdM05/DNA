import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step8
  (b d f : Point) (ABC : Circle) (FB DA DB : Line)
  (hb : b.onCircle ABC) (hf : f.isCentre ABC) (hd_noton : ¬d.onCircle ABC)
  (hfFB : f.onLine FB) (hbFB : b.onLine FB)
  (hfDA : f.onLine DA) (hdDA : d.onLine DA)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hright : ∠ f:b:d = ∟)
  : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  have hnotbDA : ¬b.onLine DA := by euclid_finish
  have htri : formTriangle b f d FB DA DB := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 b f d FB DA DB)
  euclid_finish

end Elements.Book3
