import SystemE
import Book3.Prop36.step23_notDA
import Book3.Prop36.step23_cDA
import Book3.Prop36.step23_tri
import Book3.Prop36.step23_p47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23
  (a c d e f : Point) (ABC : Circle) (DA EC EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbdca : between d c a)
  (hcEC : c.onLine EC) (heEC : e.onLine EC)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (step13 : e.isCentre ABC)
  (step17 : |(a─f)| = |(f─c)|)
  (hnotthrough : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
  (step23_assumption1 : ∠ e:f:c = ∟)
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have step23_notDA : ¬ e.onLine DA := by euclid_apply (helper_3_36_step23_notDA e ABC DA (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA); assumption)))
  have step23_cDA : c.onLine DA := by euclid_apply (helper_3_36_step23_cDA a c d DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)))
  have step23_tri : formTriangle f c e DA EC EF := by euclid_apply (helper_3_36_step23_tri a c d e f ABC DA EC EF (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show between d c a; assumption)))
  have step23_p47 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by euclid_apply (helper_3_36_step23_p47 c e f DA EC EF (by euclid_assumption "" (show formTriangle f c e DA EC EF; assumption)) (by euclid_assumption "" (show ∠ e:f:c = ∟; assumption)))
  exact step23_p47

end Elements.Book3
