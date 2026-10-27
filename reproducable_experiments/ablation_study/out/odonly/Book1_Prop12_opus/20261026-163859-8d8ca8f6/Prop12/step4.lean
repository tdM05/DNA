import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step4 (c e g h : Point) (AB CG CH CE : Line)
    (hcg1 : c.onLine CG) (hcg2 : g.onLine CG)
    (hch1 : c.onLine CH) (hch2 : h.onLine CH)
    (hce1 : c.onLine CE) (hce2 : e.onLine CE)
    (hcAB : ¬c.onLine AB) (hgAB : g.onLine AB) (heAB : e.onLine AB)
    (hehg : between e h g) :
    distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE := by
  euclid_finish

end Elements.Book1
