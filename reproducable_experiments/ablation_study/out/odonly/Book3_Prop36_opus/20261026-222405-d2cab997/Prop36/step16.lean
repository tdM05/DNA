import SystemE
import Book3.Prop18.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step16 (e b d : Point) (ABC : Circle) (DB : Line)
    (hbcirc : b.onCircle ABC) (hbDB : b.onLine DB)
    (htangent : ¬ DB.intersectsCircle ABC) (hecentre : e.isCentre ABC)
    (hdDB : d.onLine DB) (hdnotcirc : ¬ d.onCircle ABC) :
    ∠ e:b:d = ∟ := by
  have heb : e ≠ b := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  euclid_apply (proposition_18 b e ABC DB (by euclid_finish) d hdDB hdb)

end Elements.Book3
