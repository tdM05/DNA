import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step6 (a c d k : Point) (GK : Line)
  (hcsa : c.sameSide a GK) (hckd : between c k d) (hk_gk : k.onLine GK)
  : a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
