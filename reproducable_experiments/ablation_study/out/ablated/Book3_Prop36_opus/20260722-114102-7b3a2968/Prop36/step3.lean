import SystemE
import Book3.Prop18.Main

namespace Elements.Book3

theorem helper_3_36_step3 (b d f : Point) (ABC : Circle) (DB : Line)
    (h1 : f.isCentre ABC) (h2 : b.onCircle ABC) (h3 : b.onLine DB)
    (h4 : d.onLine DB) (h5 : ¬ DB.intersectsCircle ABC) (h6 : ¬ d.onCircle ABC) :
    ∠ f:b:d = ∟ := by
  have hfb : f ≠ b := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  exact Elements.Book3.proposition_18 b f ABC DB ⟨h2, h3, h5, h1, hfb⟩ d h4 hdb

end Elements.Book3
