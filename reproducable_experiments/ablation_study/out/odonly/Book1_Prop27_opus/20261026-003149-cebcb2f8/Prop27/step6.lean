import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step6
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
  (h_ae : a ≠ e)
  (h_ef : e ≠ f)
  (h_fd : f ≠ d)
  (h_a_EF : ¬a.onLine EF)
  (h_d_EF : ¬d.onLine EF)
  (h_aeb : between a e b)
  (h_asd : ¬a.sameSide d EF)
  (h_ang0 : ∠ a:e:f = ∠ e:f:d) :
  ¬(g.opposingSides b EF) := by
  intro hopp
  have hga : g.sameSide a EF := by euclid_finish
  have hng : ¬ between a e g := by euclid_finish
  have hgd : ¬ g.sameSide d EF := by euclid_finish
  have hgfd : between g f d := by euclid_finish
  euclid_apply (equal_angles e f f a g EF AE)
  euclid_apply (proposition_16 e g f d AE FD EF)
  euclid_finish

end Elements.Book1
