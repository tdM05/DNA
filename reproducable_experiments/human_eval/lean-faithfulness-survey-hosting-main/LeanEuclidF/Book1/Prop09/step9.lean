import SystemE
import Book1.Prop08.Main
import Book1.Prop09.step9_hfab
import Book1.Prop09.step9_hfac
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_9_s9 (a b c d e f : Point) (AB AC DE EF DF AF : Line)
    (ha_on_AB : a.onLine AB) (hb_on_AB : b.onLine AB)
    (hd_on_AB : d.onLine AB)
    (ha_on_AC : a.onLine AC) (hc_on_AC : c.onLine AC)
    (hbtw_adb : between a d b) (hbtw_aec : between a e c)
    (hd_on_DE : d.onLine DE) (he_on_DE : e.onLine DE)
    (he_on_EF : e.onLine EF) (hf_on_EF : f.onLine EF)
    (hd_on_DF : d.onLine DF) (hf_on_DF : f.onLine DF)
    (ha_on_AF : a.onLine AF) (hf_on_AF : f.onLine AF)
    (hf_off_DE : ¬f.onLine DE) (ha_off_DE : ¬a.onLine DE)
    (hf_opp_DE : ¬f.sameSide a DE)
    (hAB_ne_AC : AB ≠ AC)
    (hAD_eq_AE : |(a─d)| = |(a─e)|)
    (hFD_eq_DE : |(f─d)| = |(d─e)|)
    (hFE_eq_DE : |(f─e)| = |(d─e)|)
    (hDF_eq_EF : |(d─f)| = |(e─f)|) :
    ∠ d:a:f = ∠ e:a:f := by
  have s9_x4 : ¬f.onLine AB := by euclid_apply (h_1_9_s9_x1 a b c d e f AB AC DE EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show ¬f.onLine DE; assumption)) (by (show ¬a.onLine DE; assumption)) (by (show ¬f.sameSide a DE; assumption)) (by (show AB ≠ AC; assumption)) (by (show between a d b; assumption)) (by (show between a e c; assumption)) (by (show |(a─d)| = |(a─e)|; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))
  have s9_x5 : ¬f.onLine AC := by euclid_apply (h_1_9_s9_x2 a b c d e f AB AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show ¬f.onLine DE; assumption)) (by (show ¬a.onLine DE; assumption)) (by (show ¬f.sameSide a DE; assumption)) (by (show AB ≠ AC; assumption)) (by (show between a d b; assumption)) (by (show between a e c; assumption)) (by (show |(a─d)| = |(a─e)|; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))
  euclid_apply (proposition_8 a d f a e f AB DF AF AC EF AF)
  euclid_finish

end Elements.Book1
