import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6_cdf (c d e f : Point) (CD DE : Line)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (h_cde : ∠ c:d:e = ∟)
    (hc_off_de : ¬c.onLine DE)
    (hstep2 : f.onLine DE ∧ between e d f) :
    ∠ c:d:f = ∟ := by
  obtain ⟨_, hedf⟩ := hstep2
  -- ∠ e:d:c = ∟ and f on ray d→e reversed ⟹ ∠ c:d:f = ∠ e:d:c = ∟
  euclid_apply (perpendicular_onlyif e f d c DE)
  euclid_finish

end Elements.Book2
