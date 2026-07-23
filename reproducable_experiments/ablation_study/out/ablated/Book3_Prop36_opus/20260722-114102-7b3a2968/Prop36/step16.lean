import SystemE
import Book3.Prop18.Main

namespace Elements.Book3

theorem helper_3_36_step16 (b d e : Point) (ABC : Circle) (DB : Line)
    (h1 : e.isCentre ABC) (h2 : b.onCircle ABC) (h3 : b.onLine DB)
    (h4 : d.onLine DB) (h5 : ¬ DB.intersectsCircle ABC) (h6 : ¬ d.onCircle ABC) :
    ∠ e:b:d = ∟ := by
  have heb : e ≠ b := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  exact Elements.Book3.proposition_18 b e ABC DB ⟨h2, h3, h5, h1, heb⟩ d h4 hdb

end Elements.Book3
