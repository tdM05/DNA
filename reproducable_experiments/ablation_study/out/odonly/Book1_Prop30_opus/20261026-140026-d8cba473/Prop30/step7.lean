import SystemE
import Book1.Prop27.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7 (a c d g k : Point) (AB CD GK : Line)
  (ha_ab : a.onLine AB) (hg_ab : g.onLine AB) (hga : g ≠ a)
  (hk_cd : k.onLine CD) (hd_cd : d.onLine CD) (hckd : between c k d)
  (hg_gk : g.onLine GK) (hk_gk : k.onLine GK) (hgk : g ≠ k)
  (hstep6 : a.opposingSides d GK)
  (hstep5 : ∠ a:g:k = ∠ g:k:d)
  : ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1
