import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step5_par
import Book2.Prop03.step5_bef
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5 (a b c d e f : Point) (AB CD BE DE AF : Line)
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
    (h_bed : ∠ b:e:d = ∟)
    (h_eb : e ≠ b) (h_ab : a ≠ b)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(b─e)| = |(c─b)|)   -- "$BE$ (is) equal to $BC$"
    : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  -- the big rectangle AFEB viewed with corner b: sides BA and BE
  have step5_par : formParallelogram b a e f AB DE BE AF := by euclid_apply (helper_2_3_step5_par a b c d e f AB CD BE DE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  -- the angle at e between BE and DE is right (∠ b:e:d = ∟, and f is on ray e→d)
  have step5_bef : ∠ b:e:f = ∟ := by euclid_apply (helper_2_3_step5_bef b d e f BE DE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)))
  -- rectangle contained by BA and BE
  have hpair := rectangle_area b a e f AB DE BE AF ⟨step5_par, step5_bef⟩
  have heq2 := hpair.2
  -- heq2 : area△a:b:e + area△a:f:e = |b─a| * |b─e|
  have harea : Triangle.area (△ a:b:e) = Triangle.area (△ a:e:b) := area_symm_2 a b e
  rw [harea, hassump1, segment_symmetric b a, segment_symmetric c b] at heq2
  -- heq2 : area△a:e:b + area△a:f:e = |a─b| * |b─c|
  linarith [heq2]

end Elements.Book2
