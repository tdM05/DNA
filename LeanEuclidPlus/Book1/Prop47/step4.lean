import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step4
    (a b c g : Point) (AB : Line)
    (hcoffAB : ¬c.onLine AB) (hgoffAB : ¬g.onLine AB) (hgc : ¬g.sameSide c AB)
    (hassump1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟)) :
    c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟) := by
  euclid_finish

end Elements.Book1
