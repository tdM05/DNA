import SystemE
import Book3.Prop03.Main

namespace Elements.Book3

-- since EF, through the center, cuts AC, not through the center, at right-angles, it also
-- cuts it in half [Prop.~3.3]. Hence AF = FC.  EF ⊥ AC at f, e centre on EF, not on AC=DA.
-- (c.onLine DA, a ≠ c and between a f c are derived internally from the ordering d, c, a.)
theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (hconj : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧
      (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h4 : a.onCircle ABC) (h5 : c.onCircle ABC)
    (h6 : a.onLine DA) (h7 : d.onLine DA) (h8 : f.onLine DA)
    (h9 : f.onLine EF) (h10 : between d c a) :
    |(a─f)| = |(f─c)| := by
  obtain ⟨h1, h2, h3, hdis⟩ := hconj
  have hcDA : c.onLine DA := by euclid_finish
  have hbtw : between a f c := by euclid_finish
  rcases hdis with hac | hca
  · have key := (proposition_3 a c e f ABC DA EF (by euclid_finish)).2 hac
    euclid_finish
  · have key := (proposition_3 c a e f ABC DA EF (by euclid_finish)).2 hca
    euclid_finish

end Elements.Book3
