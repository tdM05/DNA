import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_45_x1
    (e₁ e₂ e₃ : Point)
    (f g k h m l : Point)
    (FG KH FK GH : Line)
    (hk_KH : k.onLine KH)
    (hh_KH : h.onLine KH)
    (hk_FK : k.onLine FK)
    (hf_FK : f.onLine FK)
    (hh_GH : h.onLine GH)
    (hgh : g ≠ h)
    (hhkf_eq : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (s9 : k.opposingSides m GH ∧ ∠ k:h:g + ∠ g:h:m = ∟ + ∟)
    (s17_a1 : |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH)
    (s18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    : ∠ f:k:m = ∠ e₁:e₂:e₃ := by

  have hGH_ne_KH : GH ≠ KH := fun heq => s9.1.1 (heq ▸ hk_KH)
  have hkh : k ≠ h := fun heq => s9.1.1 (heq ▸ hh_GH)
  have hmh : m ≠ h := fun heq => s9.1.2.1 (heq ▸ hh_GH)
  have between_k_h_m : between k h m :=
    pasch_4 k h m GH KH ⟨hGH_ne_KH, hh_GH, hh_KH, s18.1, hkh, hmh, s9.1.2.2⟩

  have hfk : f ≠ k := fun heq =>
    (Ne.symm hgh) (zero_segment_if h g
      (s17_a1.1.symm.trans (zero_segment_onlyif f k heq)))

  have hnbff : ¬between f k f := fun hbtw =>
    (between_symm f k f hbtw).2.2.1 rfl

  have hnhkm : ¬between h k m := (between_symm k h m between_k_h_m).2.2.2

  have hfkh_eq_fkm : ∠ f:k:h = ∠ f:k:m :=
    equal_angles k f f h m FK KH
      ⟨hk_FK, hf_FK, hf_FK, hk_KH, hh_KH, s18.1.2.1,
       hfk, hfk, Ne.symm hkh, Ne.symm s18.1.2.2, hnbff, hnhkm⟩

  have hfkh_sym : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  exact hfkh_eq_fkm.symm.trans (hfkh_sym.trans hhkf_eq)

end Elements.Book1
