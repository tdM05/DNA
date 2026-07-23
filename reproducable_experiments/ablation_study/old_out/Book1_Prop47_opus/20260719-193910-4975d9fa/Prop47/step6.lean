import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_47_step6 (a b c h : Point) (AB AC AH : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : c.onLine AC) (h5 : a.onLine AC) (h6 : ¬(c.onLine AB))
    (h7 : a.onLine AH) (h8 : h.onLine AH) (h9 : ¬(h.onLine AC))
    (h10 : ¬(b.onLine AC)) (h11 : ¬(h.sameSide b AC))
    (h12 : ∠ b:a:c = ∟) (h13 : ∠ c:a:h = ∟) :
    between b a h := by
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_finish

end Elements.Book1
