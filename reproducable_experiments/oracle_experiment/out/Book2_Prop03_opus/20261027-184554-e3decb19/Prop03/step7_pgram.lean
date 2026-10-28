import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- The square CDEB relabeled as formParallelogram c b d e AB DE CD BE (rectangle_area → |(c─b)|*|(c─d)|).
-- All conjuncts come from step1's square (proposition_46 outputs), reordered + sameSide symmetry.
set_option systemE.solverTime 30 in
theorem helper_2_3_step7_pgram
    (b c d e : Point) (AB DE CD BE : Line)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (heb_ne : e ≠ b)
    (hdsc_BE : d.sameSide c BE)
    (hpar_DEAB : ¬DE.intersectsLine AB) (hpar_CDBE : ¬CD.intersectsLine BE) :
    formParallelogram c b d e AB DE CD BE := by
  have hcd : c.sameSide d BE := by euclid_finish
  have hABDE : ¬AB.intersectsLine DE := fun h => hpar_DEAB (intersection_symm AB DE h)
  exact ⟨hc_AB, hb_AB, hd_DE, he_DE, hc_CD, hd_CD, ⟨hb_BE, he_BE, heb_ne.symm⟩, hcd, hABDE, hpar_CDBE⟩

end Elements.Book2
