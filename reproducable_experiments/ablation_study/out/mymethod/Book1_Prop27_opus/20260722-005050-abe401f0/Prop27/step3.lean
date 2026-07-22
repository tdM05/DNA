import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
  (h_b_AE : b.onLine AE) (h_aeb : between a e b)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_g_FD : g.onLine FD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_off : ¬a.onLine EF) (h_d_off : ¬d.onLine EF)
  (h_a_opp_d : ¬a.sameSide d EF)
  (h_angle : ∠ a:e:f = ∠ e:f:d)
  (hbd : g.sameSide b EF)
  : ∠ a:e:f = ∠ e:f:g := by
  have hgd : g.sameSide d EF := by euclid_finish
  euclid_finish

end Elements.Book1
