import SystemE
import Book1.Prop47.Main
import Book3.Prop03.Main

set_option systemE.solverTime 120

namespace Elements.Book3

theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h2 : a.onCircle ABC) (h3 : c.onCircle ABC)
    (h4 : a.onLine DA) (h5 : d.onLine DA) (h6 : f.onLine DA) (h7 : f.onLine EF)
    (h8 : between d c a) :
    |(a─f)| = |(f─c)| := by
  obtain ⟨he, heEF, henDA, hperp⟩ := h1
  have hac : a ≠ c := by euclid_finish
  -- The perpendicular EF meets AC at right-angles at f, so ∠ AFE is a right-angle.
  have haperp : ∠ a:f:e = ∟ := by euclid_finish
  have hfa : f ≠ a := by euclid_finish
  -- Pythagoras on the right-angled triangle EFA gives EA² = EF² + FA².
  euclid_apply (line_from_points e a) as EA
  euclid_apply (Elements.Book1.proposition_47 f e a EF EA DA)
  -- Since EA is a radius and EF < EA, the foot F lies inside the circle,
  have hins : f.insideCircle ABC := by euclid_finish
  -- hence F lies between the two points A and C where AC cuts the circle.
  have hb : between a f c := by euclid_finish
  -- Now Prop.~3.3 (perpendicular from the centre bisects the chord) applies.
  have hkey := (Elements.Book3.proposition_3 a c e f ABC DA EF (by euclid_finish)).2 haperp
  euclid_finish

end Elements.Book3
