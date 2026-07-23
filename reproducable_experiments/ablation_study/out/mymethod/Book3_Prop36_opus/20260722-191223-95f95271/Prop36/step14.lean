import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step14
  (a c e f : Point) (ABC : Circle) (DA EF : Line)
  (hf_DA : f.onLine DA) (hperp : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hecenter : e.isCentre ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  : f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hef : e ≠ f := by
    intro heq
    exact hnotthrough ⟨e, hecenter, heq ▸ hf_DA⟩
  euclid_finish

end Elements.Book3
