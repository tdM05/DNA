import SystemE
import Book3.Prop33.hdaq_btw
import Book3.Prop33.hdaq_ray
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hdaq
    (a b d e0 q : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_q_AE : q.onLine AE) (h_qb : q.sameSide b AD) (h_da : d ≠ a) :
    ∠ d:a:q = ∟ := by
  by_cases hbtw : between q a e0
  · have hdaq_btw : ∠ d:a:q = ∟ := by euclid_apply (helper_3_33_hdaq_btw a b d e0 q AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show q.onLine AE; assumption)) (by euclid_assumption "" (show q.sameSide b AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show between q a e0; assumption)))
    exact hdaq_btw
  · have hdaq_ray : ∠ d:a:q = ∟ := by euclid_apply (helper_3_33_hdaq_ray a b d e0 q AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show q.onLine AE; assumption)) (by euclid_assumption "" (show q.sameSide b AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ between q a e0; assumption)))
    exact hdaq_ray

end Elements.Book3
