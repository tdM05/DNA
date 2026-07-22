import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step3
  (b f d : Point) (ABC : Circle) (DB : Line)
  (hb : b.onCircle ABC) (hbDB : b.onLine DB) (hnint : ¬ DB.intersectsCircle ABC)
  (hfcentre : f.isCentre ABC) (hdDB : d.onLine DB) (hdnoton : ¬ d.onCircle ABC)
  : ∠ f:b:d = ∟ := by
  euclid_apply (proposition_18 b f ABC DB)
  euclid_finish

end Elements.Book3
