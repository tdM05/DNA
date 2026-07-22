import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bkhm (g h k m : Point) (GH KH HM : Line)
    (a3 : k.onLine KH) (a4 : h.onLine KH) (a8 : h.onLine GH)
    (b2 : m.onLine HM) (hstep10 : KH = HM)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    : between k h m := by
  euclid_finish

end Elements.Book1
