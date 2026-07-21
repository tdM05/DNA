import SystemE
import Book1.Prop27.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7
    (AB CD GK : Line) (a c d g k : Point)
    (haAB : a.onLine AB) (hgAB : g.onLine AB) (hga : g ≠ a)
    (hgGK : g.onLine GK) (hkGK : k.onLine GK) (hgk : g ≠ k)
    (hkCD : k.onLine CD) (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hckd : between c k d)
    (hstep5 : ∠ a:g:k = ∠ g:k:d)
    (hstep6 : a.opposingSides d GK)
    : ¬(AB.intersectsLine CD) := by
  -- prop27: alternate angles equal + opposite sides ⟹ AB ∥ CD
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1
