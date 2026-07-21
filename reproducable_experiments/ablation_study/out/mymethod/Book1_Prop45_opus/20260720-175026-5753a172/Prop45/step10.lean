import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step10
  (g h k m : Point) (GH KH HM : Line)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
  (hh_KH : h.onLine KH) (hk_KH : k.onLine KH)
  (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
  (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟)) :
  KH = HM := by
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_finish

end Elements.Book1
