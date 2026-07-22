import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step10 (g h k m : Point) (GH KH HM : Line)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hmHM : m.onLine HM) (hhHM : h.onLine HM)
    (hkGH : ¬ k.onLine GH) (hmGH : ¬ m.onLine GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟)) :
    KH = HM := by
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_finish

end Elements.Book1
