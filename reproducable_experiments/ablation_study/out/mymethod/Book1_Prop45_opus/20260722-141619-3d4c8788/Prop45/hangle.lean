import SystemE
import Book1.Prop45.step21_bkhm

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle (e₁ e₂ e₃ f g h k m : Point) (FK GH KH HM : Line)
    (a3 : k.onLine KH) (a4 : h.onLine KH) (a7 : g.onLine GH) (a8 : h.onLine GH)
    (a5 : f.onLine FK) (a6 : k.onLine FK) (a9 : g ≠ h)
    (b2 : m.onLine HM) (hstep10 : KH = HM)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hstep17_assumption1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (hkf : ∠ h:k:f = ∠ e₁:e₂:e₃)
    : ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  have step21_bkhm : between k h m := by euclid_apply (helper_1_45_step21_bkhm g h k m GH KH HM (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)))
  euclid_finish

end Elements.Book1
