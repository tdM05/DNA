import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3 (EF CD GK : Line) (g h k e f c d a : Point)
  (hg_gk : g.onLine GK)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hk_cd : k.onLine CD) (hk_gk : k.onLine GK)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hehf : between e h f)
  (hc_cd : c.onLine CD) (hd_cd : d.onLine CD) (hckd : between c k d)
  (hea_ss : e.sameSide a GK) (hca_ss : c.sameSide a GK)
  (hghk : between g h k)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$"
  : ∠ g:h:f = ∠ g:k:d := by
  have hcd_ef : ¬(CD.intersectsLine EF) := hassump1.2.2
  -- construct y on GK beyond k (between h k y)
  have hhk_ne : h ≠ k := by
    intro heq
    euclid_apply (intersection_lines_common_point h CD EF)
    euclid_finish
  euclid_apply (extend_point GK h k) as y
  -- f and d lie on the same side of GK (e↔c same side via a; e,f opposite; c,d opposite)
  have hfd : f.sameSide d GK := by euclid_finish
  -- proposition 1.29 on parallels EF, CD with transversal GK
  euclid_apply (proposition_29 e f c d g y h k EF CD GK)
  euclid_finish

end Elements.Book1
