import SystemE
import Book1.Prop27.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7 (AB CD GK : Line) (a g k d c : Point)
  (ha_ab : a.onLine AB) (hg_ab : g.onLine AB)
  (hk_cd : k.onLine CD) (hd_cd : d.onLine CD)
  (hg_gk : g.onLine GK) (hk_gk : k.onLine GK)
  (hga_ne : g ≠ a) (hgk_ne : g ≠ k) (hckd : between c k d)
  (hstep6 : a.opposingSides d GK) (hstep5 : ∠ a:g:k = ∠ g:k:d) :
  ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1
