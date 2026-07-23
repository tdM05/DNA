import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_tri (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbtw_dca : between d c a)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_EC : e.onLine EC) (hc_EC : c.onLine EC)
  (he_centre : e.isCentre ABC) (hc_circ : c.onCircle ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hbisect : |(a─f)| = |(f─c)|)
  (hassump1 : ∠ e:f:c = ∟)
  : formTriangle f e c EF EC DA := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have hec : e ≠ c := by euclid_finish
  have hfc : f ≠ c := by euclid_finish
  have hfe : f ≠ e := by euclid_finish
  euclid_finish

end Elements.Book3
