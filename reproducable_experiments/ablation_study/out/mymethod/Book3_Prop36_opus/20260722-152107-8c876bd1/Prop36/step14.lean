import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step14 (a c e f : Point) (ABC : Circle) (DA EF : Line)
  (hf_DA : f.onLine DA)
  (hangle : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_centre : e.isCentre ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  : f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hene : ¬ e.onLine DA := fun hon => hnotthrough ⟨e, he_centre, hon⟩
  have hdist : distinctPointsOnLine e f EF := by euclid_finish
  exact ⟨hf_DA, hdist, hangle⟩

end Elements.Book3
