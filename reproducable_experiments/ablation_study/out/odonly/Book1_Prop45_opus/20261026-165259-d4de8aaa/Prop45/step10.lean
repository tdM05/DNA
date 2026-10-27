import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step10 (g h k m : Point) (GH KH HM : Line)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hhKH : h.onLine KH) (hkKH : k.onLine KH)
  (hhHM : h.onLine HM) (hmHM : m.onLine HM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : KH = HM := by
  obtain ⟨hopp, hang⟩ := hstep9
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_finish

end Elements.Book1
