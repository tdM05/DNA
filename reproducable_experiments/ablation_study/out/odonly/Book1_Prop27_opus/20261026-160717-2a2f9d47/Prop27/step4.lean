import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4
  (a e f b g : Point) (AE EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_b_AE : b.onLine AE) (h_g_AE : g.onLine AE)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_ef : e ≠ f)
  (h_aeb : between a e b)
  (h_a_nEF : ¬a.onLine EF)
  (hbd : g.sameSide b EF)
  (step3 : ∠ a:e:f = ∠ e:f:g)
  : False := by
  have hge : between g e a := by euclid_finish
  have hfg : f ≠ g := by euclid_finish
  euclid_apply (line_from_points f g) as FG
  have htri : formTriangle f g e FG AE EF := by euclid_finish
  euclid_apply (proposition_16 f g e a FG AE EF)
  euclid_finish

end Elements.Book1
