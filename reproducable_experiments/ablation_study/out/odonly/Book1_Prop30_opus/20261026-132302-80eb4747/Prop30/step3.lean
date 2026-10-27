import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3 (a c d e f g h k : Point) (AB CD EF GK : Line)
  (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hk_CD : k.onLine CD) (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
  (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
  (hgk : g ≠ k) (hghk : between g h k) (hehf : between e h f) (hckd : between c k d)
  (he_ss : e.sameSide a GK) (hc_ss : c.sameSide a GK)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$"
  : ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (proposition_29'''' f d g h k EF CD GK)
  euclid_finish

end Elements.Book1
