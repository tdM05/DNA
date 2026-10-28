import SystemE
import Book2.Prop03.step5_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step5_pgram : formParallelogram b a e f AB DE BE AF := by euclid_apply (helper_2_3_step5_pgram a b c d e f AB CD DE BE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)))
  have hbef : ∠ b:e:f = ∟ := by euclid_finish
  have hrect : Triangle.area △ a:b:e + Triangle.area △ a:f:e = |(b─a)| * |(b─e)| := by
    euclid_apply (rectangle_area b a e f AB DE BE AF)
    euclid_finish
  have hsymm_area : Triangle.area △ a:f:e = Triangle.area △ a:e:f := by euclid_finish
  have hsymm_len : |(b─a)| = |(a─b)| := by euclid_finish
  rw [hsymm_area, hsymm_len, hassump1] at hrect
  exact hrect

end Elements.Book2
