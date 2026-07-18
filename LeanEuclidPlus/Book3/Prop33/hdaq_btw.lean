import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hdaq_btw
    (a b d e0 q : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_q_AE : q.onLine AE) (h_qb : q.sameSide b AD) (h_da : d ≠ a)
    (h_btw : between q a e0) :
    ∠ d:a:q = ∟ := by
  have he0a : e0 ≠ a := by euclid_finish
  have hqa : q ≠ a := by euclid_finish
  have hdAE : ¬ d.onLine AE := by euclid_finish
  euclid_apply (perpendicular_onlyif e0 q a d AE)
  euclid_finish

end Elements.Book3
