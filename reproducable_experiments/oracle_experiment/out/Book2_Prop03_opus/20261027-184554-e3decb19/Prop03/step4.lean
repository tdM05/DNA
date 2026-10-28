import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_3_step4
    (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hcd_len : |(c─d)| = |(c─b)|) (heb_ne : e ≠ b)
    (hang_bcd : ∠ b:c:d = ∟) (hang_cbe : ∠ c:b:e = ∟) (hdsc_BE : d.sameSide c BE)
    (hd_CD : d.onLine CD) (hf_DE : f.onLine DE) (he_DE : e.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hpar_DEAB : ¬DE.intersectsLine AB)
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:b:e + Triangle.area △ a:e:f =
      (Triangle.area △ a:c:d + Triangle.area △ a:d:f) +
      (Triangle.area △ c:b:e + Triangle.area △ c:e:d) := by
  obtain ⟨_, hbet_edf⟩ := hstep2
  have step4_pgram : formParallelogram a b f e AB DE AF BE := by sorry
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  euclid_finish

end Elements.Book2
