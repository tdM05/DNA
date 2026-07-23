import SystemE
import Book3.Prop18.Main

namespace Elements.Book3

theorem helper_3_36_step16 (b d e : Point) (ABC : Circle) (DB : Line)
    (h1 : b.onCircle ABC) (h2 : b.onLine DB) (h3 : ¬ DB.intersectsCircle ABC)
    (h4 : e.isCentre ABC) (h5 : d.onLine DB) (h6 : d.outsideCircle ABC) :
    ∠ e:b:d = ∟ := by
  euclid_apply (proposition_18 b e ABC DB)
  euclid_finish

end Elements.Book3
