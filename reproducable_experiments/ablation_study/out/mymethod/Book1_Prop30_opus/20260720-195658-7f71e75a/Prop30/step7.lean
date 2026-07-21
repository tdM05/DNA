import SystemE
import Book1.Prop27.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7 (AB CD GK : Line) (a d g k c : Point)
  (ha_AB : a.onLine AB) (hg_AB : g.onLine AB)
  (hk_CD : k.onLine CD) (hd_CD : d.onLine CD) (hc_CD : c.onLine CD)
  (hg_GK : g.onLine GK) (hk_GK : k.onLine GK)
  (hga : g ≠ a) (hgk : g ≠ k) (hckd : between c k d)
  (hstep6 : a.opposingSides d GK)
  (hstep5 : ∠ a:g:k = ∠ g:k:d) :
    ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1
