import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step14
  (a c e f : Point) (ABC : Circle) (DA EF : Line)
  (he : e.isCentre ABC)
  (hnot : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hfDA : f.onLine DA)
  (hdisj : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  : f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hne : ¬e.onLine DA := by
    intro hmem
    exact hnot ⟨e, he, hmem⟩
  refine ⟨hfDA, ?_, hdisj⟩
  euclid_finish

end Elements.Book3
