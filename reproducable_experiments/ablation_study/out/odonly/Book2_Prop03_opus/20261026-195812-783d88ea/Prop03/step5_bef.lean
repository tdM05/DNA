import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5_bef (b d e f : Point) (BE DE : Line)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (h_bed : ∠ b:e:d = ∟)
    (h_eb : e ≠ b)
    (hstep2 : f.onLine DE ∧ between e d f) :
    ∠ b:e:f = ∟ := by
  obtain ⟨_, hedf⟩ := hstep2
  -- move the second ray's point from d to f along DE (both beyond e on the same side)
  euclid_apply (equal_angles e b b d f BE DE)
  euclid_finish

end Elements.Book2
