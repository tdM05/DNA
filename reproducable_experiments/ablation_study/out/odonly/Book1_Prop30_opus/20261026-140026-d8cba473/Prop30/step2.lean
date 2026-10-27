import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2 (a e f g h k : Point) (AB EF GK : Line)
  (ha_ab : a.onLine AB) (hg_ab : g.onLine AB) (hga : g ≠ a)
  (hg_gk : g.onLine GK) (hh_gk : h.onLine GK)
  (hh_ef : h.onLine EF) (hf_ef : f.onLine EF)
  (hehf : between e h f) (hesa : e.sameSide a GK)
  (hghk : between g h k)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$"
  : ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (proposition_29''' a f g h AB EF GK)
  euclid_finish

end Elements.Book1
