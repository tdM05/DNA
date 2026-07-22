import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_pa
  (a e f : Point) (DA EF : Line)
  (haDA : a.onLine DA) (hfDA : f.onLine DA)
  (hnotDA : ¬ e.onLine DA)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (hafe : ∠ a:f:e = ∟)
  (hfa : f ≠ a)
  : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| := by
  have hfe : f ≠ e := by euclid_finish
  euclid_apply (line_from_points e a) as EA
  have htri : formTriangle f a e DA EA EF := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 f a e DA EA EF)
  euclid_finish

end Elements.Book3
