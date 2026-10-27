import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step4 (c d : Point) (DC : Line)
  (h_d_DC : d.onLine DC) (h_c_DC : c.onLine DC)
  : d.onLine DC ∧ c.onLine DC := by exact ⟨h_d_DC, h_c_DC⟩

end Elements.Book1
