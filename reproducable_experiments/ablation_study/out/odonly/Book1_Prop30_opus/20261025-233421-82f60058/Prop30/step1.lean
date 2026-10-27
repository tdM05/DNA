import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1
    (a c e g h k : Point) (AB CD EF GK : Line)
    (hgAB : g.onLine AB) (hgGK : g.onLine GK)
    (hhEF : h.onLine EF) (hhGK : h.onLine GK)
    (hkCD : k.onLine CD) (hkGK : k.onLine GK)
    (haAB : a.onLine AB) (heEF : e.onLine EF) (hcCD : c.onLine CD)
    (hea : e.sameSide a GK) (hca : c.sameSide a GK) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1
