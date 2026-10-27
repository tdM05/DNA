import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_foff_be (c d e f : Point) (BE DE : Line)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (he_BE : e.onLine BE)
    (hdc_BE : d.sameSide c BE)
    (hstep2 : f.onLine DE ∧ between e d f) :
    ¬f.onLine BE := by
  intro hf
  -- DE ≠ BE: d ∈ DE but d ∉ BE (from d.sameSide c BE)
  have hDEne : DE ≠ BE := by
    intro h; rw [h] at hd_DE; euclid_finish
  -- f, e are common to BE and DE; if f ≠ e they'd force BE = DE
  have hfe : f = e := by
    by_contra hne
    euclid_apply (two_points_determine_line f e BE DE)
    euclid_finish
  -- but between e d f ⟹ e ≠ f
  euclid_finish

end Elements.Book2
