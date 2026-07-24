import SystemE
import Book3.Prop18.Main

namespace Elements.Book3

-- (angle) FBD is a right-angle [Prop.~3.18]: DB touches ABC at b, and FB is joined
-- from the centre f to the point of contact b, so FB ⊥ DB, i.e. ∠ f:b:d = ∟.
theorem helper_3_36_step3 (b d f : Point) (ABC : Circle) (DB : Line)
    (h1 : b.onCircle ABC) (h2 : b.onLine DB) (h3 : ¬ DB.intersectsCircle ABC)
    (h4 : f.isCentre ABC) (h5 : d.onLine DB) (h6 : ¬ d.onCircle ABC) :
    ∠ f:b:d = ∟ := by
  have hdb : d ≠ b := by euclid_finish
  have key := proposition_18 b f ABC DB (by euclid_finish)
  exact key d h5 hdb

end Elements.Book3
