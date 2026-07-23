import SystemE

namespace Elements.Book3

-- $EF$ is the perpendicular from the centre $E$ to $AC$, its foot $F$ lying on $DA$.  Since $E$ is
-- the centre and $DCA$ is NOT through the centre, $E$ is off line $DA$, so $E \ne F$ and $EF$ is a
-- genuine (distinct-points) line.
theorem helper_3_36_step14 (a c e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : f.onLine DA)
    (h2 : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)
    (h3 : e.onLine EF) (h4 : f.onLine EF)
    (h5 : e.isCentre ABC)
    (h6 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA)) :
    f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  have hoff : ¬e.onLine DA := fun he => h6 ⟨e, h5, he⟩
  euclid_finish

end Elements.Book3
