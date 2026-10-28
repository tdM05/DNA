import SystemE
import Book2.Prop03.step6_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6
    (a b c d e f : Point) (AB CD DE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hcd_len : |(c─d)| = |(c─b)|)
    (hang_bcd : ∠ b:c:d = ∟) (hang_cde : ∠ c:d:e = ∟)
    (hd_CD : d.onLine CD) (hd_DE : d.onLine DE) (hf_DE : f.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (hpar_DEAB : ¬DE.intersectsLine AB)
    (hstep2 : f.onLine DE ∧ between e d f)
    (hassump1 : |(d─c)| = |(c─b)|) :
    Triangle.area △ a:c:d + Triangle.area △ a:d:f = |(a─c)| * |(c─b)| := by
  obtain ⟨_, hbet_edf⟩ := hstep2
  have step6_pgram : formParallelogram c a d f AB DE CD AF := by euclid_apply (helper_2_3_step6_pgram a b c d e f AB CD DE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)))
  have hcdf : ∠ c:d:f = ∟ := by euclid_finish
  have hrect : Triangle.area △ a:c:d + Triangle.area △ a:f:d = |(c─a)| * |(c─d)| := by
    euclid_apply (rectangle_area c a d f AB DE CD AF)
    euclid_finish
  have hsymm_area : Triangle.area △ a:f:d = Triangle.area △ a:d:f := by euclid_finish
  have hsymm_len : |(c─a)| = |(a─c)| := by euclid_finish
  have hcd_cb : |(c─d)| = |(c─b)| := by euclid_finish
  rw [hsymm_area, hsymm_len, hcd_cb] at hrect
  exact hrect

end Elements.Book2
