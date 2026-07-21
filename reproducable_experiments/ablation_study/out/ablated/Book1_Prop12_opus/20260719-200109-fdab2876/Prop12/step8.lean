import SystemE
import Book1.Prop08.Main

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (hg : g.onLine AB) (he : e.onLine AB)
    (hehg : between e h g) (hc : ¬(c.onLine AB))
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hgh : |(g─h)| = |(h─e)|) (hcg : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
