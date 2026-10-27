import SystemE
import Book1.Prop16.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4 (a b d e f g : Point) (AE FD EF : Line)
  (hae_a : a.onLine AE) (hae_e : e.onLine AE) (hae_b : b.onLine AE) (hae_g : g.onLine AE)
  (hfd_f : f.onLine FD) (hfd_d : d.onLine FD) (hfd_g : g.onLine FD) (hfd_ne : f ≠ d)
  (hef_e : e.onLine EF) (hef_f : f.onLine EF) (hef_ne : e ≠ f)
  (ha_off : ¬a.onLine EF) (hd_off : ¬d.onLine EF) (hna_sd : ¬a.sameSide d EF)
  (hbet : between a e b)
  (hbd : g.sameSide b EF)
  (hstep3 : ∠ a:e:f = ∠ e:f:g)
  : False := by
  euclid_apply (proposition_16 f g e a FD AE EF)
  euclid_finish

end Elements.Book1
