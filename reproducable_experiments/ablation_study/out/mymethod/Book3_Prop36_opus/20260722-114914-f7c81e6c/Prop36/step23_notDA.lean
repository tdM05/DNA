import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_notDA
  (e : Point) (ABC : Circle) (DA : Line)
  (step13 : e.isCentre ABC)
  (hnotthrough : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
  : ¬ e.onLine DA := by
  intro he
  exact hnotthrough ⟨e, step13, he⟩

end Elements.Book3
