import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_3_step5
    (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hcd_len : |(c─d)| = |(c─b)|) (heb_ne : e ≠ b)
    (hang_bcd : ∠ b:c:d = ∟) (hang_cbe : ∠ c:b:e = ∟) (hang_bed : ∠ b:e:d = ∟)
    (hdsc_BE : d.sameSide c BE)
    (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (hf_DE : f.onLine DE) (he_DE : e.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hpar_DEAB : ¬DE.intersectsLine AB)
    (hstep2 : f.onLine DE ∧ between e d f)
    (hassump1 : |(b─e)| = |(b─c)|) :
    Triangle.area △ a:b:e + Triangle.area △ a:e:f = |(a─b)| * |(b─c)| := by
  obtain ⟨_, hbet_edf⟩ := hstep2
  have step5_pgram : formParallelogram b a e f AB DE BE AF := by sorry
  have hbef : ∠ b:e:f = ∟ := by euclid_finish
  have hrect : Triangle.area △ a:b:e + Triangle.area △ a:f:e = |(b─a)| * |(b─e)| := by
    euclid_apply (rectangle_area b a e f AB DE BE AF)
    euclid_finish
  have hsymm_area : Triangle.area △ a:f:e = Triangle.area △ a:e:f := by euclid_finish
  have hsymm_len : |(b─a)| = |(a─b)| := by euclid_finish
  rw [hsymm_area, hsymm_len, hassump1] at hrect
  exact hrect

end Elements.Book2
