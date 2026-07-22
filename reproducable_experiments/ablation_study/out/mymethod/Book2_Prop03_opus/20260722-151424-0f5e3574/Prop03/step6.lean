import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step6_par
import Book2.Prop03.step6_rangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD DE AF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟)
    (hcde : ∠ c:d:e = ∟) (hstep2 : f.onLine DE ∧ between e d f)
    (hAFCD : ¬(AF.intersectsLine CD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hcd_eq : |(c─d)| = |(c─b)|) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  obtain ⟨_, hedf⟩ := hstep2
  have step6_par : formParallelogram c a d f AB DE CD AF := by euclid_apply (helper_2_3_step6_par a b c d f AB CD DE AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have step6_rangle : ∠ c:d:f = ∟ := by euclid_apply (helper_2_3_step6_rangle a b c d e f CD DE (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show between e d f; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have hrect := (rectangle_area c a d f AB DE CD AF ⟨step6_par, step6_rangle⟩).2
  have hs1 : Triangle.area △ a:c:d = Triangle.area △ a:d:c := area_symm_2 a c d
  have hs2 : |(c─a)| = |(a─c)| := segment_symmetric c a
  rw [hs2, hcd_eq] at hrect
  rw [hs1] at hrect
  linarith [hrect]

end Elements.Book2
