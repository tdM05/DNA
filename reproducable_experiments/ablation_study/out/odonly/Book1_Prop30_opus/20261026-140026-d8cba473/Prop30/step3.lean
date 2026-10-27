import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3 (a c d e f g h k : Point) (CD EF GK : Line)
  (hh_ef : h.onLine EF) (hf_ef : f.onLine EF)
  (hk_cd : k.onLine CD) (hd_cd : d.onLine CD)
  (hg_gk : g.onLine GK) (hh_gk : h.onLine GK) (hk_gk : k.onLine GK)
  (hghk : between g h k)
  (hehf : between e h f) (hesa : e.sameSide a GK)
  (hckd : between c k d) (hcsa : c.sameSide a GK)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$"
  : ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (proposition_29'''' f d g h k EF CD GK)
  euclid_finish

end Elements.Book1
