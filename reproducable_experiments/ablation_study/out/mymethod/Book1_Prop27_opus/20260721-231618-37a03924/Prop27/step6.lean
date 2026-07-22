import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step6
  (a b d e f g : Point) (AE FD EF : Line)
  (ha_AE : a.onLine AE) (he_AE : e.onLine AE) (hae : a ≠ e)
  (hb_AE : b.onLine AE) (hab : between a e b)
  (hg_AE : g.onLine AE) (hg_FD : g.onLine FD)
  (hf_FD : f.onLine FD) (hd_FD : d.onLine FD) (hfd : f ≠ d)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hef : e ≠ f)
  (ha_EF : ¬a.onLine EF) (hd_EF : ¬d.onLine EF)
  (had : ¬a.sameSide d EF)
  (hangle : ∠ a:e:f = ∠ e:f:d)
  : ¬(g.opposingSides b EF) := by
  intro hopp
  have hga : g.sameSide a EF := by euclid_finish
  have hang : ∠ g:e:f = ∠ a:e:f := by euclid_finish
  have htri : formTriangle e g f AE FD EF := by euclid_finish
  have hbet : between g f d := by euclid_finish
  euclid_apply (proposition_16 e g f d AE FD EF)
  euclid_finish

end Elements.Book1
