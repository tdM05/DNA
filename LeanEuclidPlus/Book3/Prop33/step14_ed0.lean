import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14_ed0
    (a d d0 e : Point) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_d0_AD : d0.onLine AD)
    (h_dad0 : between d a d0) (h_dae : ∠ d:a:e = ∟)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_ea : e ≠ a) (h_ADAE : AD ≠ AE) :
    ∠ e:a:d0 = ∟ := by
  have he_AD : ¬ e.onLine AD := by
    intro heAD
    euclid_apply (two_points_determine_line a e AE AD)
    euclid_finish
  euclid_apply (perpendicular_onlyif d d0 a e AD)
  euclid_finish

end Elements.Book3
