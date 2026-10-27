import SystemE

namespace Elements.Book1

theorem proposition_30 : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) := by
  sorry

end Elements.Book1
