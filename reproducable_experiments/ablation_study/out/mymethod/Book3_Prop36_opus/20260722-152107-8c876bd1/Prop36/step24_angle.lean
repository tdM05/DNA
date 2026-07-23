import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_angle (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbtw_dca : between d c a)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_centre : e.isCentre ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hbisect : |(a─f)| = |(f─c)|)
  (hangle_c : ∠ e:f:c = ∟)
  : ∠ e:f:d = ∟ := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  have hbtw_dcf : between d c f := by euclid_finish
  euclid_apply (equal_angles f c d e e DA EF)
  euclid_finish

end Elements.Book3
