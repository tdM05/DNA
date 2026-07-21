import SystemE
import Book1.Prop08.Main

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (h1 : c.onLine CG) (h2 : g.onLine CG)
    (h3 : c.onLine CH) (h4 : h.onLine CH)
    (h5 : c.onLine CE) (h6 : e.onLine CE)
    (h7 : e.onLine AB) (h8 : g.onLine AB) (h9 : e ≠ g)
    (h10 : ¬ c.onLine AB) (h11 : between e h g)
    (h12 : |(g─h)| = |(h─e)|) (h13 : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
