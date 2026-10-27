import SystemE
import Book2.Prop03.step2_hef
import Book2.Prop03.step2_coff_de
import Book2.Prop03.step2_foff
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2 (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hbetween : between a c b)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hf_DE : f.onLine DE)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (hdc_BE : d.sameSide c BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_cde : ∠ c:d:e = ∟)
    (h_ab : a ≠ b) (h_eb : e ≠ b) :
    f.onLine DE ∧ between e d f := by
  refine ⟨hf_DE, ?_⟩
  -- e and f are on opposite sides of CD (sub-node)
  have step2_hef : ¬(e.sameSide f CD) := by euclid_apply (helper_2_3_step2_hef a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- c is off DE (sub-node), so CD ≠ DE
  have step2_coff_de : ¬c.onLine DE := by euclid_apply (helper_2_3_step2_coff_de b c d e AB BE DE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- f is off CD (sub-node), so f ≠ d (since d ∈ CD)
  have step2_foff : ¬f.onLine CD := by euclid_apply (helper_2_3_step2_foff a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  have hCDne : CD ≠ DE := by intro h; rw [h] at hc_CD; exact step2_coff_de hc_CD
  have hfd : f ≠ d := by intro h; rw [h] at step2_foff; exact step2_foff hd_CD
  -- e ≠ d (d is off BE, e is on BE)
  have hed : e ≠ d := by intro h; rw [h] at he_BE; euclid_finish
  -- D lies on CD and DE, so D is between E and F on line DE (pasch_4)
  euclid_apply (pasch_4 e d f CD DE)
  euclid_finish

end Elements.Book2
