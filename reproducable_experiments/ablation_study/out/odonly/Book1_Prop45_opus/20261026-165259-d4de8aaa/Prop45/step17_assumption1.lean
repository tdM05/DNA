import SystemE
import Book1Variants.Prop34

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step17_assumption1 (f g k h : Point) (FG KH FK GH : Line)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH)
  (hni1 : ¬FG.intersectsLine KH) (hni2 : ¬FK.intersectsLine GH)
  : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH) := by
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_finish

end Elements.Book1
