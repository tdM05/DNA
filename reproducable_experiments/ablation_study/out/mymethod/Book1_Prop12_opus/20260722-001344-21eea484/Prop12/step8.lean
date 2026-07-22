import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (hcAB : ¬c.onLine AB)
    (heAB : e.onLine AB) (hgAB : g.onLine AB)
    (hbet : between e h g) (heg : e ≠ g)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hstep4 : distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE)
    (hstep6 : |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)|)
    (hstep7 : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
