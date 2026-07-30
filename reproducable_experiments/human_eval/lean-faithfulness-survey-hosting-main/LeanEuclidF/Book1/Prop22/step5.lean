import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_22_s5 (f d : Point) (DKL : Circle)
    (hcen : f.isCentre DKL) (hon : d.onCircle DKL) :
    f.isCentre DKL ∧ d.onCircle DKL := ⟨hcen, hon⟩

end Elements.Book1
