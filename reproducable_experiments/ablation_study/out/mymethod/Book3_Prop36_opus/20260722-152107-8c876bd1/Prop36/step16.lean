import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step16 (b e d : Point) (ABC : Circle) (DB : Line)
  (hb_circ : b.onCircle ABC) (hb_DB : b.onLine DB) (hnint : ¬DB.intersectsCircle ABC)
  (he_centre : e.isCentre ABC) (hd_DB : d.onLine DB) (hd_out : ¬d.onCircle ABC)
  : ∠ e:b:d = ∟ := by
  have heb : e ≠ b := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  euclid_apply (proposition_18 b e ABC DB (by euclid_finish) d hd_DB hdb)

end Elements.Book3
