import SystemE
import Helpers.SameSide

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19_kmss (f g h k l m : Point) (FG KH FK GH : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a5 : f.onLine FK) (a6 : k.onLine FK)
    (a7 : g.onLine GH) (a8 : h.onLine GH) (a9 : g ≠ h)
    (a10 : f.sameSide k GH)
    (a11 : ¬FG.intersectsLine KH) (a12 : ¬FK.intersectsLine GH)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    : k.sameSide m FG := by
  have hpsm := parallelogram_same_side f g k h FG KH FK GH ⟨a1, a2, a3, a4, a5, a6, ⟨a7, a8, a9⟩, a10, a11, a12⟩
  have hfsg : f.sameSide g KH := hpsm.2.2
  have hfoff : ¬f.onLine KH := same_side_not_on_line f g KH hfsg
  have hmKH : m.onLine KH := hstep18.1.2.1
  exact sameSide_of_parallel k m f KH FG a3 hmKH a1 hfoff a11

end Elements.Book1
