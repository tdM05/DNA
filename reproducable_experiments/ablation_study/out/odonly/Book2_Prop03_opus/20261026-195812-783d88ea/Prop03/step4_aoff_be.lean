import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_aoff_be (a b c d : Point) (AB BE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hb_BE : b.onLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_ab : a ≠ b) :
    ¬a.onLine BE := by
  intro ha
  -- a,b are two distinct points on both AB and BE ⟹ AB = BE
  euclid_apply (two_points_determine_line a b AB BE)
  -- then c ∈ AB = BE, contradicting d.sameSide c BE (which needs c ∉ BE)
  euclid_finish

end Elements.Book2
