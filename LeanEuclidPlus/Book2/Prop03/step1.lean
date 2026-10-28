import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step1
    (b c d e : Point) (AB DE CD BE : Line)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (heb : e ≠ b)
    (hdsc : d.sameSide c BE)
    (hnDEAB : ¬DE.intersectsLine AB) (hnCDBE : ¬CD.intersectsLine BE)
    (hcd : |(c─d)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|) (hde : |(d─e)| = |(c─b)|)
    (hang : ∠ b:c:d = ∟) :
    formParallelogram d e c b DE AB CD BE ∧
      |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧ ∠ b:c:d = ∟ := by
  exact ⟨⟨hd_DE, he_DE, hc_AB, hb_AB, hd_CD, hc_CD, ⟨he_BE, hb_BE, heb⟩, hdsc, hnDEAB, hnCDBE⟩,
    hcd, hbe, hde, hang⟩

end Elements.Book2
