import SystemE

namespace Elements.Book1

theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) := by
  sorry

end Elements.Book1
