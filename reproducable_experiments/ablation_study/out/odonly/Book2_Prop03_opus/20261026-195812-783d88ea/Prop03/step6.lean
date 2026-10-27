import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step6_par
import Book2.Prop03.step2_coff_de
import Book2.Prop03.step6_cdf
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hbetween : between a c b)
    (hstep2 : f.onLine DE ∧ between e d f)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_cde : ∠ c:d:e = ∟)
    (h_eb : e ≠ b) (h_ab : a ≠ b)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(c─d)| = |(c─b)|)   -- "$DC$ (is) equal to $CB$"
    : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  -- the left rectangle ACDF viewed with corner c: sides CA and CD
  have step6_par : formParallelogram c a d f AB DE CD AF := by euclid_apply (helper_2_3_step6_par a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- c is off DE (reused), needed for the right-angle transfer at d
  have step2_coff_de : ¬c.onLine DE := by euclid_apply (helper_2_3_step2_coff_de b c d e AB BE DE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- the angle at d between CD and DE is right (∠ c:d:e = ∟, f on ray d→e reversed)
  have step6_cdf : ∠ c:d:f = ∟ := by euclid_apply (helper_2_3_step6_cdf c d e f CD DE (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ¬c.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)))
  -- rectangle contained by CA and CD
  have hpair := rectangle_area c a d f AB DE CD AF ⟨step6_par, step6_cdf⟩
  have heq2 := hpair.2
  -- heq2 : area△a:c:d + area△a:f:d = |c─a| * |c─d|
  have harea : Triangle.area (△ a:c:d) = Triangle.area (△ a:d:c) := area_symm_2 a c d
  rw [harea, hassump1, segment_symmetric c a] at heq2
  -- heq2 : area△a:d:c + area△a:f:d = |a─c| * |c─b|
  linarith [heq2]

end Elements.Book2
