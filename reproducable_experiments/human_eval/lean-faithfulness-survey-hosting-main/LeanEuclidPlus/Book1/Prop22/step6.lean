import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_22_s6 (g h : Point) (KLH : Circle)
    (hcen : g.isCentre KLH) (hon : h.onCircle KLH) :
    g.isCentre KLH ∧ h.onCircle KLH := ⟨hcen, hon⟩

end Elements.Book1
