import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step6
    (a b d e f g : Point) (AE FD EF : Line)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hbAE : b.onLine AE) (hgAE : g.onLine AE)
    (hgFD : g.onLine FD) (hfFD : f.onLine FD) (hdFD : d.onLine FD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hef : e ≠ f)
    (hanEF : ¬a.onLine EF) (hdnEF : ¬d.onLine EF) (hassd : ¬a.sameSide d EF)
    (haeb : between a e b)
    (hang : ∠ a:e:f = ∠ e:f:d) :
    ¬(g.opposingSides b EF) := by
  intro hopp
  euclid_apply (proposition_16 e g f d AE FD EF)
  euclid_finish

end Elements.Book1
