import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle (e₁ e₂ e₃ f g h k m : Point) (KH GH FK HM : Line)
    (hangle_eq : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (hstep17a1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH)) (hgh : g ≠ h)
    (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hmHM : m.onLine HM) (hstep10 : KH = HM)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hfFK : f.onLine FK) (hkFK : k.onLine FK) :
    ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  have hmKH : m.onLine KH := by euclid_finish
  have hbkhm : between k h m := by euclid_finish
  have hlen : |(f─k)| = |(h─g)| := hstep17a1.1
  have hfk : f ≠ k := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hray : ∠ f:k:h = ∠ f:k:m := by
    euclid_apply (equal_angles k f f h m FK KH)
    euclid_finish
  have hsymm : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  rw [← hray, hsymm, hangle_eq]

end Elements.Book1
