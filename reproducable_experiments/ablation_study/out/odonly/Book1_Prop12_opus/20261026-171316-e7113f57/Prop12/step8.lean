import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line) (EFG : Circle)
    (hcAB : ¬c.onLine AB) (heAB : e.onLine AB) (hgAB : g.onLine AB)
    (hbet : between e h g)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hcentre : c.isCentre EFG) (hgC : g.onCircle EFG) (heC : e.onCircle EFG)
    (hgh : |(e─h)| = |(h─g)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB)
  euclid_finish

end Elements.Book1
