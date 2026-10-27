import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step16 (b d e : Point) (ABC : Circle) (DB : Line)
  (hbC : b.onCircle ABC) (hbDB : b.onLine DB) (hDBtan : ¬DB.intersectsCircle ABC)
  (he : e.isCentre ABC) (hdDB : d.onLine DB)
  (hdin : ¬d.insideCircle ABC) (hdnc : ¬d.onCircle ABC) :
    ∠ e:b:d = ∟ := by
  euclid_apply (proposition_18 b e ABC DB (by euclid_finish) d (by euclid_finish) (by euclid_finish))

end Elements.Book3
