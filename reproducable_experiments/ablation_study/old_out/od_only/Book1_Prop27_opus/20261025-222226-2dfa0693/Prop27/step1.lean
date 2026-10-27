import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1
    (a b d e f g : Point) (AE FD EF : Line)
    (hint : AE.intersectsLine FD)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hgAE : g.onLine AE) (hbAE : b.onLine AE)
    (hgFD : g.onLine FD) (hfFD : f.onLine FD) (hdFD : d.onLine FD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hef : e ≠ f)
    (hanEF : ¬a.onLine EF) (hdnEF : ¬d.onLine EF) (haeb : between a e b) :
    g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
