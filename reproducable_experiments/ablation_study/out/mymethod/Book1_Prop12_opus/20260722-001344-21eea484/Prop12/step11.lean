import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (heAB : e.onLine AB) (hgAB : g.onLine AB) (hhAB : h.onLine AB)
    (hcAB : ¬c.onLine AB)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hbet : between e h g)
    (hstep10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  by_cases hah : a = h
  · -- a coincides with h; use b (which is ≠ h since a ≠ b)
    right
    by_cases hbb : between e h b
    · euclid_apply (equal_angles h g b c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e b c c AB CH)
      euclid_finish
  · left
    by_cases hba : between e h a
    · euclid_apply (equal_angles h g a c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e a c c AB CH)
      euclid_finish

end Elements.Book1
