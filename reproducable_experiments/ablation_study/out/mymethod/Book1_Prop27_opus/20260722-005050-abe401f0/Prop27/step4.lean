import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
  (h_b_AE : b.onLine AE) (h_aeb : between a e b) (h_g_AE : g.onLine AE)
  (h_f_FD : f.onLine FD) (h_g_FD : g.onLine FD) (h_d_FD : d.onLine FD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_off : ¬a.onLine EF) (h_d_off : ¬d.onLine EF)
  (h_a_opp_d : ¬a.sameSide d EF)
  (hbd : g.sameSide b EF)
  (step3 : ∠ a:e:f = ∠ e:f:g)
  : False := by
  have hgea : between a e g := by euclid_finish
  euclid_apply (proposition_16 f g e a FD AE EF)
  euclid_finish

end Elements.Book1
