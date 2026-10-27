import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4
    (a b e f g : Point) (AE FD EF : Line)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hbAE : b.onLine AE) (hgAE : g.onLine AE)
    (hfFD : f.onLine FD) (hgFD : g.onLine FD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hef : e ≠ f)
    (hanEF : ¬a.onLine EF)
    (haeb : between a e b) (hgsb : g.sameSide b EF)
    (hang : ∠ a:e:f = ∠ e:f:g) :
    False := by
  euclid_apply (proposition_16 f g e a FD AE EF)
  euclid_finish

end Elements.Book1
