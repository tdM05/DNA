import SystemE

namespace Elements.Book3

theorem proposition_19 : ∀ (a c e : Point) (ABC : Circle) (DE CA : Line),
  c.onLine DE ∧ c.onCircle ABC ∧ ¬ DE.intersectsCircle ABC ∧
  a.onLine CA ∧ c.onLine CA ∧ a ≠ c ∧
  e.onLine DE ∧ e ≠ c ∧ ∠ a:c:e = ∟ →
  ∀ f : Point, f.isCentre ABC → f.onLine CA := by
  sorry

end Elements.Book3
