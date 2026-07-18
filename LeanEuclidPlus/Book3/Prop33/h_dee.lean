import SystemE
import Book3.Prop33.h_dee_btw
import Book3.Prop33.h_dee_ray
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_h_dee
    (a d e0 ee g : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_ee_AE : ee.onLine AE) (h_eega : between ee g a) (h_da : d ≠ a) :
    ∠ d:a:ee = ∟ := by
  by_cases hbtw : between ee a e0
  · have h_dee_btw : ∠ d:a:ee = ∟ := by euclid_apply (helper_3_33_h_dee_btw a d e0 ee g AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ee.onLine AE; assumption)) (by euclid_assumption "" (show between ee g a; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show between ee a e0; assumption)))
    exact h_dee_btw
  · have h_dee_ray : ∠ d:a:ee = ∟ := by euclid_apply (helper_3_33_h_dee_ray a d e0 ee g AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ee.onLine AE; assumption)) (by euclid_assumption "" (show between ee g a; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ between ee a e0; assumption)))
    exact h_dee_ray

end Elements.Book3
