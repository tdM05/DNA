import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2 (a e f g h k : Point) (AB EF GK : Line)
  (ha_AB : a.onLine AB) (hg_AB : g.onLine AB) (hga : g ≠ a)
  (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
  (he_ss : e.sameSide a GK) (hehf : between e h f) (hghk : between g h k)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$"
  : ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (proposition_29''' a f g h AB EF GK)
  euclid_finish

end Elements.Book1
