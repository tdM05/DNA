import SystemE
import Book3.Prop33.step3_btw
import Book3.Prop33.step3_ray
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step3
    (a d e e0 g : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_e_AE : e.onLine AE) (h_ega : between e g a) (h_da : d ≠ a) :
    ∠ d:a:e = ∟ := by
  by_cases hbtw : between e a e0
  · have step3_btw : ∠ d:a:e = ∟ := by euclid_apply (helper_3_33_step3_btw a d e e0 g AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show between e a e0; assumption)))
    exact step3_btw
  · have step3_ray : ∠ d:a:e = ∟ := by euclid_apply (helper_3_33_step3_ray a d e e0 g AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ between e a e0; assumption)))
    exact step3_ray

end Elements.Book3
