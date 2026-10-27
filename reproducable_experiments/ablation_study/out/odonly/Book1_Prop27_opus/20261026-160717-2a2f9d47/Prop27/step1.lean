import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_g_AE : g.onLine AE) (h_b_AE : b.onLine AE)
  (h_ae : a ≠ e) (h_aeb : between a e b)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_g_FD : g.onLine FD) (h_fd : f ≠ d)
  (h_a_nEF : ¬a.onLine EF) (h_d_nEF : ¬d.onLine EF)
  (hassump1 : AE.intersectsLine FD)
  : g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
