import SystemE
import Helpers.SameSide
import Helpers.OffLine
import Book2.Prop03.step6_anotcd
import Book2.Prop03.step6_fnotab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_par (a b c d f : Point) (AB CD DE AF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (hf_DE : f.onLine DE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟)
    (hAFCD : ¬(AF.intersectsLine CD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hcd_eq : |(c─d)| = |(c─b)|) :
    formParallelogram c a d f AB DE CD AF := by
  have step6_anotcd : ¬(a.onLine CD) := by euclid_apply (helper_2_3_step6_anotcd a b c d AB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have step6_fnotab : ¬(f.onLine AB) := by euclid_apply (helper_2_3_step6_fnotab a b c d f AB CD DE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have hne_AFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF step6_anotcd
  have hne_CDAF : CD ≠ AF := hne_AFCD.symm
  have hCDAF : ¬(CD.intersectsLine AF) := fun h => hAFCD (intersection_symm CD AF h)
  have h_ss : c.sameSide d AF :=
    sameSide_of_parallel_both c d CD AF hc_CD hd_CD hne_CDAF hCDAF
  have haf_ne : a ≠ f := fun h => step6_fnotab (h ▸ ha_AB)
  have hABDE : ¬(AB.intersectsLine DE) := fun h => hDEAB (intersection_symm AB DE h)
  exact ⟨hc_AB, ha_AB, hd_DE, hf_DE, hc_CD, hd_CD, ⟨ha_AF, hf_AF, haf_ne⟩, h_ss, hABDE, hCDAF⟩

end Elements.Book2
