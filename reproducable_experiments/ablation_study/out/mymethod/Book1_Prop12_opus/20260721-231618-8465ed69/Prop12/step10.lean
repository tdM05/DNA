import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step10 (c e g h : Point) (AB : Line)
  (hcAB : ¬c.onLine AB) (heAB : e.onLine AB) (hgAB : g.onLine AB)
  (hbet : between e h g)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ c:h:g = ∠ e:h:c)   -- "the adjacent angles equal to one another"
  : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟ := by
  euclid_apply (perpendicular_if g e h c AB)
  euclid_finish

end Elements.Book1
