import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2
  (AB EF GK : Line) (a b e f g h k : Point)
  (hg_AB : g.onLine AB) (hg_GK : g.onLine GK)
  (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
  (hk_GK : k.onLine GK)
  (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hagb : between a g b) (hehf : between e h f)
  (he_ss : e.sameSide a GK)
  (hEFAB : EF ≠ AB)
  (hc : between g h k)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$"
  : ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (extend_point GK h g) as g0
  euclid_apply (proposition_29 a b e f g0 k g h AB EF GK)
  euclid_finish

end Elements.Book1
