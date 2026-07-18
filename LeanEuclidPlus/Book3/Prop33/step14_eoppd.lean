import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14_eoppd
    (a b d d0 e : Point) (AB AD : Line)
    (h_a_AB : a.onLine AB) (h_d_AD : d.onLine AD) (h_a_AD : a.onLine AD)
    (h_d0_AD : d0.onLine AD) (h_dad0 : between d a d0)
    (h_e_off : ¬ e.onLine AB)
    (h_bd0_side : e.sameSide d0 AB)
    (h_bad : ∠ b:a:d < ∟) (h_b_AB : b.onLine AB) :
    e.opposingSides d AB := by
  euclid_apply (pasch_3 d a d0 AB)
  euclid_finish

end Elements.Book3
