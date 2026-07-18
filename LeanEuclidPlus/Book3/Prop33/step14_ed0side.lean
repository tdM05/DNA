import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14_ed0side
    (a b d d0 e e0 g : Point) (α : Circle) (AB AD AE : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_d0_AD : d0.onLine AD)
    (h_dad0 : between d a d0)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_ega : between e g a) (h_de0 : ∠ d:a:e0 = ∟)
    (h_dae : ∠ d:a:e = ∟) (h_bad : ∠ b:a:d < ∟)
    (h_ebAD : e.sameSide b AD) (h_ed0 : ∠ e:a:d0 = ∟) :
    e.sameSide d0 AB := by
  euclid_finish

end Elements.Book3
