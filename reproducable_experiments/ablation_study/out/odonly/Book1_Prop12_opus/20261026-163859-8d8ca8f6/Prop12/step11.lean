import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (heAB : e.onLine AB) (hgAB : g.onLine AB) (hhAB : h.onLine AB)
    (hcAB : ¬c.onLine AB) (hehg : between e h g)
    (hc_CH : c.onLine CH) (hh_CH : h.onLine CH)
    (hstep10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  obtain ⟨hcg, hec⟩ := hstep10
  have key : ∀ p : Point, p.onLine AB → p ≠ h → ∠ p:h:c = ∟ := by
    intro p hpAB hph
    by_cases hbp : between e h p
    · euclid_apply (equal_angles h g p c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e p c c AB CH)
      euclid_finish
  by_cases hah : a = h
  · right
    have hbh : b ≠ h := fun hb => hab (hah.trans hb.symm)
    exact key b hbAB hbh
  · left
    exact key a haAB hah

end Elements.Book1
