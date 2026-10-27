import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle_bkm (h k m : Point) (GH KH : Line)
    (hh_GH : h.onLine GH) (hh_KH : h.onLine KH)
    (hk_KH : k.onLine KH) (hm_KH : m.onLine KH)
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH)) :
    between k h m := by
  euclid_finish

end Elements.Book1
