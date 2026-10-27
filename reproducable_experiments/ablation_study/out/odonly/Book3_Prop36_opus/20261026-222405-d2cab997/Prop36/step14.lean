import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step14 (a c e f : Point) (ABC : Circle) (DA EF : Line)
    (hfDA : f.onLine DA)
    (hangles : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hecentre : e.isCentre ABC)
    (hnotthrough : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA)) :
    f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hennotDA : ¬ e.onLine DA := fun h => hnotthrough ⟨e, hecentre, h⟩
  refine ⟨hfDA, ?_, hangles⟩
  euclid_finish

end Elements.Book3
