import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step3
    (a b d e f g : Point) (AE FD EF : Line)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hbAE : b.onLine AE) (hgAE : g.onLine AE)
    (hgFD : g.onLine FD) (hfFD : f.onLine FD) (hdFD : d.onLine FD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hef : e ≠ f)
    (hanEF : ¬a.onLine EF) (hdnEF : ¬d.onLine EF) (hassd : ¬a.sameSide d EF)
    (haeb : between a e b) (hgsb : g.sameSide b EF)
    (hang : ∠ a:e:f = ∠ e:f:d) :
    ∠ a:e:f = ∠ e:f:g := by
  euclid_finish

end Elements.Book1
