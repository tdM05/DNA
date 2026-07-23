import SystemE
import Book3.Prop36.step24_angle
import Book3.Prop36.step24_tri
import Book3.Prop36.step24_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA EF ED : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbtw_dca : between d c a)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (he_centre : e.isCentre ABC) (hd_notinside : ¬ d.insideCircle ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hbisect : |(a─f)| = |(f─c)|)
  (hangle_c : ∠ e:f:c = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have step24_angle : ∠ e:f:d = ∟ := by euclid_apply (helper_3_36_step24_angle a c d e f ABC DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show ∠ e:f:c = ∟; assumption)))
  have step24_tri : formTriangle f e d EF ED DA := by euclid_apply (helper_3_36_step24_tri a c d e f ABC DA EF ED (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ d.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)))
  have step24_pyth : |(e─d)| * |(e─d)| = |(e─f)| * |(e─f)| + |(f─d)| * |(f─d)| := by euclid_apply (helper_3_36_step24_pyth d e f DA EF ED (by euclid_assumption "" (show formTriangle f e d EF ED DA; assumption)) (by euclid_assumption "" (show ∠ e:f:d = ∟; assumption)))
  rw [segment_symmetric d f, segment_symmetric f e]
  rw [step24_pyth]; ring

end Elements.Book3
