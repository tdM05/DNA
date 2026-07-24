import SystemE

namespace Elements.Book3

-- EF drawn from E, perpendicular to AC [Prop.~1.12]: f is the perpendicular foot (from
-- proposition_12) on line DA (= AC), and EF joins e to f. e is the centre. Since DCA is NOT
-- through the centre, e is not on DA, hence e ≠ f (f is on DA).
theorem helper_3_36_step14 (a c e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : f.onLine DA) (h2 : (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h3 : e.onLine EF) (h4 : f.onLine EF)
    (h5 : e.isCentre ABC)
    (h6 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA)) :
    f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hne : ¬ e.onLine DA := fun h => h6 ⟨e, h5, h⟩
  euclid_finish

end Elements.Book3
