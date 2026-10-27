import SystemE

namespace Elements.Book1

theorem proposition_37' : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  sorry

end Elements.Book1
