import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_ang2 (CD EF GK : Line) (a c d e f h k : Point)
  (hk_cd : k.onLine CD) (hk_gk : k.onLine GK)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hc_cd : c.onLine CD) (hd_cd : d.onLine CD) (hckd : between c k d)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hehf : between e h f)
  (hca_ss : c.sameSide a GK) (hea_ss : e.sameSide a GK)
  (hcd_ef : ¬CD.intersectsLine EF) (hne_cd_ef : CD ≠ EF) :
  ∠ c:k:h = ∠ k:h:f := by
  have hkh_ne : k ≠ h := by
    intro heq
    euclid_apply (intersection_lines_common_point k CD EF)
    euclid_finish
  -- extension points on GK: p2 before k (between p2 k h), q2 beyond h (between k h q2)
  euclid_apply (extend_point GK h k) as p2
  euclid_apply (extend_point GK k h) as q2
  -- d and f on the same side of GK (c~e via a; c,d opposite; e,f opposite)
  have hdf : d.sameSide f GK := by euclid_finish
  -- proposition 1.29 on parallels CD, EF with transversal GK (crossings k, h)
  euclid_apply (proposition_29 c d e f p2 q2 k h CD EF GK)
  euclid_finish

end Elements.Book1
