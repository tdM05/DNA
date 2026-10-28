import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step7_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7
    (b c d e : Point) (AB DE CD BE : Line)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE) (heb_ne : e ≠ b)
    (hdsc_BE : d.sameSide c BE)
    (hpar_DEAB : ¬DE.intersectsLine AB) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hang_cde : ∠ c:d:e = ∟) (hcd_len : |(c─d)| = |(c─b)|) :
    Triangle.area △ c:b:e + Triangle.area △ c:e:d = |(c─b)| * |(c─b)| := by
  have step7_pgram : formParallelogram c b d e AB DE CD BE := by euclid_apply (helper_2_3_step7_pgram b c d e AB DE CD BE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)))
  have hrect : Triangle.area △ c:d:e + Triangle.area △ c:b:e = |(c─b)| * |(c─d)| := by
    euclid_apply (rectangle_area c b d e AB DE CD BE)
    euclid_finish
  have hsymm_area : Triangle.area △ c:d:e = Triangle.area △ c:e:d := by euclid_finish
  rw [hcd_len] at hrect
  linarith [hrect, hsymm_area]

end Elements.Book2
