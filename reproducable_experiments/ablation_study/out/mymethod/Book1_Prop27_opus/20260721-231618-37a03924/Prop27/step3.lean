import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
  (a b d e f g : Point) (AE FD EF : Line)
  (ha_AE : a.onLine AE) (he_AE : e.onLine AE) (hae : a ≠ e)
  (hb_AE : b.onLine AE) (hab : between a e b)
  (hg_AE : g.onLine AE) (hg_FD : g.onLine FD)
  (hf_FD : f.onLine FD) (hd_FD : d.onLine FD) (hfd : f ≠ d)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hef : e ≠ f)
  (ha_EF : ¬a.onLine EF) (hd_EF : ¬d.onLine EF)
  (had : ¬a.sameSide d EF)
  (hangle : ∠ a:e:f = ∠ e:f:d)
  (hbd : g.sameSide b EF)
  : ∠ a:e:f = ∠ e:f:g := by euclid_finish

end Elements.Book1
