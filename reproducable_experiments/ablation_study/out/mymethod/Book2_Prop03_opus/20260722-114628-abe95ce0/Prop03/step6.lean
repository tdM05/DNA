import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Mathlib.Tactic.Linarith
import Book2.Prop03.step6_para
import Book2.Prop03.step6_ang

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD DE AF : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hc_ab : c.onLine AB) (hab : a ≠ b)
    (hbet : between a c b)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hc_cd : c.onLine CD) (hd_cd : d.onLine CD)
    (ha_af : a.onLine AF) (hf_af : f.onLine AF) (hpar_af : ¬AF.intersectsLine CD)
    (hpar_deab : ¬DE.intersectsLine AB)
    (hang : ∠ b:c:d = ∟) (hlen : |(c─d)| = |(c─b)|) (hang_cde : ∠ c:d:e = ∟)
    (hstep2 : f.onLine DE ∧ between e d f)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(c─d)| = |(c─b)|)   -- "$DC$ (is) equal to $CB$"
    : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  obtain ⟨hf_de, hbet2⟩ := hstep2
  have hcd : c ≠ d := by euclid_finish
  have step6_para : formParallelogram c a d f AB DE CD AF := by euclid_apply (helper_2_3_step6_para a b c d f AB CD DE AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have step6_ang : ∠ c:d:f = ∟ := by euclid_apply (helper_2_3_step6_ang c d e f DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show between e d f; assumption)))
  have hrect := rectangle_area c a d f AB DE CD AF ⟨step6_para, step6_ang⟩
  obtain ⟨_, hrect2⟩ := hrect
  have hca : |(c─a)| = |(a─c)| := by euclid_finish
  have hadc : Triangle.area △ a:c:d = Triangle.area △ a:d:c := by euclid_finish
  rw [hca, hassump1] at hrect2
  rw [hadc] at hrect2
  linarith [hrect2]

end Elements.Book2
