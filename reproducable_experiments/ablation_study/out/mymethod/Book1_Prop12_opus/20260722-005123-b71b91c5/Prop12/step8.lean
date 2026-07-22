import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (hcAB : ¬c.onLine AB) (heAB : e.onLine AB) (hgAB : g.onLine AB)
    (hbet : between e h g)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hgh : |(g─h)| = |(h─e)|) (hbase : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  have hT1 : formTriangle h g c AB CG CH := by euclid_finish
  have hT2 : formTriangle h e c AB CE CH := by euclid_finish
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
