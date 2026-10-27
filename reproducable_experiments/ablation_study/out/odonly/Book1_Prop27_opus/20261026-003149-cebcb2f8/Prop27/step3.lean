import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
  (a d e f b g : Point)
  (AE FD EF : Line)
  (h_a_AE : a.onLine AE)
  (h_e_AE : e.onLine AE)
  (h_b_AE : b.onLine AE)
  (h_g_AE : g.onLine AE)
  (h_f_FD : f.onLine FD)
  (h_d_FD : d.onLine FD)
  (h_g_FD : g.onLine FD)
  (h_e_EF : e.onLine EF)
  (h_f_EF : f.onLine EF)
  (h_ef : e ≠ f)
  (h_fd : f ≠ d)
  (h_a_EF : ¬a.onLine EF)
  (h_d_EF : ¬d.onLine EF)
  (h_aeb : between a e b)
  (h_asd : ¬a.sameSide d EF)
  (h_ang0 : ∠ a:e:f = ∠ e:f:d)
  (hbd : g.sameSide b EF) :
  ∠ a:e:f = ∠ e:f:g := by
  have hgd : g.sameSide d EF := by euclid_finish
  have hnb : ¬ between g f d := by euclid_finish
  euclid_apply (equal_angles f e e g d EF FD)
  euclid_finish

end Elements.Book1
