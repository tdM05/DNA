import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3
    (a c d e f g h k : Point) (CD EF GK : Line)
    (hgGK : g.onLine GK) (hhGK : h.onLine GK) (hkGK : k.onLine GK)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hehf : between e h f)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hckd : between c k d)
    (hghk : between g h k)
    (hea : e.sameSide a GK) (hca : c.sameSide a GK)
    (hCDEF : ¬CD.intersectsLine EF)
    (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF)) :
    ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (extend_point GK h k) as q
  euclid_apply (proposition_29 e f c d g q h k EF CD GK)
  euclid_finish

end Elements.Book1
