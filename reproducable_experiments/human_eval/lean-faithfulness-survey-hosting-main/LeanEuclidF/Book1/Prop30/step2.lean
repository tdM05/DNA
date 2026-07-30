import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_30_s2
    (AB EF GK : Line) (a b e f g h k : Point)
    (hg_AB : g.onLine AB) (hg_GK : g.onLine GK)
    (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
    (hk_GK : k.onLine GK)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (hbetw_ghk : between g h k)
    (heside : e.sameSide a GK)
    (hnopar : ¬AB.intersectsLine EF)
    (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))
    : ∠ a:g:k = ∠ g:h:f := by

  have hbf : b.sameSide f GK := by euclid_finish

  euclid_apply (proposition_29'' a b f g h AB EF GK)

  euclid_finish

end Elements.Book1
