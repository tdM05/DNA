import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle_eq (f g h k m : Point) (FG KH FK GH : Line)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hk_KH : k.onLine KH) (hm_KH : m.onLine KH) (hh_KH : h.onLine KH)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hk_notGH : ¬(k.onLine GH)) (hgh_ne : g ≠ h)
    (hni_FGKH : ¬(FG.intersectsLine KH))
    (hbkm : between k h m) :
    ∠ f:k:m = ∠ f:k:h := by
  have hgKH : ¬ g.onLine KH := by euclid_finish
  have hFGKH : FG ≠ KH := by euclid_finish
  have hfk : f ≠ k := by euclid_finish
  euclid_apply (equal_angles k f f m h FK KH)
  euclid_finish

end Elements.Book1
