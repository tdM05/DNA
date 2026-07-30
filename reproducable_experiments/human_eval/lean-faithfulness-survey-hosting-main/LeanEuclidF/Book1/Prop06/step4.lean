import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s4 (d c : Point) (DC : Line) (hd : d.onLine DC) (hc : c.onLine DC) :
    d.onLine DC ∧ c.onLine DC := by
  exact ⟨hd, hc⟩

end Elements.Book1
