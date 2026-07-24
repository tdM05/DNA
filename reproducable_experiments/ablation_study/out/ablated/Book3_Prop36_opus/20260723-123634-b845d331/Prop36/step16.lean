import SystemE
import Book3.Prop18.Main

namespace Elements.Book3

-- (Angle) EBD (is) thus a right-angle [Prop.~3.18]: DB touches ABC at b, and EB is joined
-- from the centre e to the point of contact b, so EB ⊥ DB, i.e. ∠ e:b:d = ∟.
theorem helper_3_36_step16 (b d e : Point) (ABC : Circle) (DB : Line)
    (h1 : b.onCircle ABC) (h2 : b.onLine DB) (h3 : ¬ DB.intersectsCircle ABC)
    (h4 : e.isCentre ABC) (h5 : d.onLine DB) (h6 : ¬ d.onCircle ABC) :
    ∠ e:b:d = ∟ := by
  have hdb : d ≠ b := by euclid_finish
  have key := proposition_18 b e ABC DB (by euclid_finish)
  exact key d h5 hdb

end Elements.Book3
