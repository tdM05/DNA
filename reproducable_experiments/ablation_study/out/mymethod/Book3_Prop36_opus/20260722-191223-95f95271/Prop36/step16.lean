import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step16
  (b d e : Point) (ABC : Circle) (DB : Line)
  (hb_circ : b.onCircle ABC) (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (hnint : ¬ DB.intersectsCircle ABC) (hecenter : e.isCentre ABC)
  (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC)
  : ∠ e:b:d = ∟ := by
  euclid_apply (Elements.Book3.proposition_18 b e ABC DB)
  euclid_finish

end Elements.Book3
