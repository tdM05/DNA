import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step3 (c : Point) (CF AD : Line)
    (hc_cf : c.onLine CF) (hcf_ad : ¬(CF.intersectsLine AD)) :
    c.onLine CF ∧ ¬(CF.intersectsLine AD) :=
  ⟨hc_cf, hcf_ad⟩

end Elements.Book2
