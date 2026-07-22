import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_facts
  (a c d : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hbdca : between d c a)
  : c.onLine DA ∧ a ≠ c := by
  have hcDA : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  exact ⟨hcDA, hac⟩

end Elements.Book3
