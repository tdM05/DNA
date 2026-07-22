import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hgAB : g.onLine AB) (heAB : e.onLine AB)
    (hhAB : h.onLine AB) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcAB : ¬c.onLine AB) (hab : a ≠ b) (hbet : between e h g)
    (hstep10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  by_cases hah : a = h
  · right
    by_cases hbeb : between e h b
    · euclid_apply (equal_angles h g b c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e b c c AB CH)
      euclid_finish
  · left
    by_cases hbea : between e h a
    · euclid_apply (equal_angles h g a c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e a c c AB CH)
      euclid_finish

end Elements.Book1
