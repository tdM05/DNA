import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_47_step6 (a b c h : Point) (AB AC AH : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : a.onLine AC) (h5 : c.onLine AC)
    (h6 : a.onLine AH) (h7 : h.onLine AH)
    (h8 : ¬(h.onLine AC)) (h9 : ¬(b.onLine AC)) (h10 : ¬(h.sameSide b AC))
    (h11 : ∠ b:a:c = ∟) (h12 : ∠ c:a:h = ∟) (h13 : ¬(c.onLine AB)) :
    between b a h := by
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_finish

end Elements.Book1
