import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1 (a d e f b g : Point) (AE FD EF : Line)
  (hae_a : a.onLine AE) (hae_e : e.onLine AE)
  (hfd_f : f.onLine FD) (hfd_d : d.onLine FD) (hfd_ne : f ≠ d)
  (hef_e : e.onLine EF) (hef_f : f.onLine EF) (hef_ne : e ≠ f)
  (ha_off : ¬a.onLine EF) (hd_off : ¬d.onLine EF)
  (hb_ae : b.onLine AE) (hbet : between a e b)
  (hg_ae : g.onLine AE) (hg_fd : g.onLine FD)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AE.intersectsLine FD)   -- "For if not"
  : g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
