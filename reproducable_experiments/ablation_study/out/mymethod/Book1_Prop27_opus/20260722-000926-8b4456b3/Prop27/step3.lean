import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
  (a d e f g b : Point) (AE FD EF : Line)
  (h_e_AE : e.onLine AE) (h_a_AE : a.onLine AE) (h_b_AE : b.onLine AE) (h_g_AE : g.onLine AE)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_g_FD : g.onLine FD) (h_fd : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_EF : ¬a.onLine EF) (h_d_EF : ¬d.onLine EF) (h_ad : ¬a.sameSide d EF)
  (h_aeb : between a e b)
  (h_gb : g.sameSide b EF)
  (h_ang : ∠ a:e:f = ∠ e:f:d)
  : ∠ a:e:f = ∠ e:f:g := by
  -- b and d land on the same side of EF (a↔b opposite via e on EF; a↔d opposite by hypothesis).
  have hgd : g.sameSide d EF := by euclid_finish
  -- since g,d are on the same side of EF and both on FD which meets EF at f, f is not between them.
  have hnbtw : ¬ between d f g := by euclid_finish
  have hgf : g ≠ f := by euclid_finish
  -- rays f→d and f→g coincide, so the angles ∠e:f:d and ∠e:f:g are equal.
  have hangeq : ∠ e:f:d = ∠ e:f:g := by
    euclid_apply (equal_angles f e e d g EF FD)
    euclid_finish
  euclid_finish

end Elements.Book1
