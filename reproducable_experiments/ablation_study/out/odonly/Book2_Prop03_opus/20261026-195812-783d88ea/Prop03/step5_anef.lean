import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5_anef (a b c d e f : Point) (AB BE DE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_eb : e ≠ b) :
    a ≠ f := by
  intro h
  -- DE ≠ AB (if DE = AB then e,b force BE = AB ⟹ c ∈ BE, contra d.sameSide c BE)
  have hDEne : DE ≠ AB := by
    intro hh
    rw [hh] at hd_DE he_DE
    euclid_apply (two_points_determine_line e b BE AB)
    euclid_finish
  -- a = f ∈ DE, and a ∈ AB ⟹ AB meets DE
  have ha_DE : a.onLine DE := h.symm ▸ hf_DE
  euclid_apply (intersection_lines_common_point a AB DE)
  euclid_finish

end Elements.Book2
