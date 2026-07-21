import SystemE
import Book1.Prop08.Main

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (h1 : g.onLine CG) (h2 : c.onLine CG)
    (h3 : h.onLine CH) (h4 : c.onLine CH)
    (h5 : e.onLine CE) (h6 : c.onLine CE)
    (h7 : g.onLine AB) (h8 : e.onLine AB) (h9 : ¬(c.onLine AB))
    (h10 : between e h g) (h11 : e ≠ g)
    (h12 : |(g─h)| = |(h─e)|) (h13 : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
