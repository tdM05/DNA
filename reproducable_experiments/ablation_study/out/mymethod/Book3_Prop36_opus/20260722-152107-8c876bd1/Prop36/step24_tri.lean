import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_tri (a c d e f : Point) (ABC : Circle) (DA EF ED : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbtw_dca : between d c a)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (he_centre : e.isCentre ABC) (hd_notinside : ¬ d.insideCircle ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hbisect : |(a─f)| = |(f─c)|)
  : formTriangle f e d EF ED DA := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  have hfd : f ≠ d := by euclid_finish
  have hfe : f ≠ e := by euclid_finish
  euclid_finish

end Elements.Book3
