import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2_coff_de (b c d e : Point) (AB BE DE : Line)
    (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_eb : e ≠ b) :
    ¬c.onLine DE := by
  -- DE ≠ AB:  if DE = AB then e,b on AB ⟹ BE = AB ⟹ c ∈ BE, contradicting d.sameSide c BE
  have hDEne : DE ≠ AB := by
    intro h
    rw [h] at hd_DE he_DE
    euclid_apply (two_points_determine_line e b BE AB)
    euclid_finish
  -- c on DE would put c ∈ DE ∩ AB, forcing DE to meet AB
  intro hc
  euclid_apply (intersection_lines_common_point c DE AB)
  euclid_finish

end Elements.Book2
