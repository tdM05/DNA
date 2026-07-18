import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step3_ray
    (a d e e0 g : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_e_AE : e.onLine AE) (h_ega : between e g a) (h_da : d ≠ a)
    (h_ray : ¬ between e a e0) :
    ∠ d:a:e = ∟ := by
  have hea : e ≠ a := by euclid_finish
  euclid_apply (equal_angles a d d e e0 AD AE)
  euclid_finish

end Elements.Book3
