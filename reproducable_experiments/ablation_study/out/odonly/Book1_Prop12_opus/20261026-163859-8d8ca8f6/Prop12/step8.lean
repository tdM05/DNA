import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line)
    (hcAB : ¬c.onLine AB) (hgAB : g.onLine AB) (heAB : e.onLine AB)
    (hehg : between e h g)
    (hcg1 : c.onLine CG) (hcg2 : g.onLine CG)
    (hch1 : c.onLine CH) (hch2 : h.onLine CH)
    (hce1 : c.onLine CE) (hce2 : e.onLine CE)
    (hgh : |(g─h)| = |(h─e)|) (hcge : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h g c h e c AB CG CH AB CE CH)
  euclid_finish

end Elements.Book1
