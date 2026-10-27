import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2
    (a b e f g h k : Point) (AB EF GK : Line)
    (hgAB : g.onLine AB) (hgGK : g.onLine GK)
    (hkGK : k.onLine GK) (hgk : g ≠ k)
    (hhEF : h.onLine EF) (hhGK : h.onLine GK)
    (haAB : a.onLine AB) (hga : g ≠ a)
    (hbAB : b.onLine AB) (hagb : between a g b)
    (heEF : e.onLine EF) (hea : e.sameSide a GK)
    (hfEF : f.onLine EF) (hehf : between e h f)
    (hABEF : ¬AB.intersectsLine EF)
    (hghk : between g h k)
    (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF)) :
    ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (extend_point GK k g) as p
  euclid_apply (proposition_29 a b e f p k g h AB EF GK)
  euclid_finish

end Elements.Book1
