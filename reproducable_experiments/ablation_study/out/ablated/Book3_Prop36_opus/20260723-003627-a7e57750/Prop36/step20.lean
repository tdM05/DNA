import SystemE
import Book1.Prop47.Main
import Book2.Prop06.Main

namespace Elements.Book3

-- $AC$ is cut in half at the foot $F$ (steps 18/19) and $CD$ is added straight-on (order
-- $A$-$C$-$D$, i.e. `between d c a`).  As in step 17, we re-establish that $F$ lies strictly between
-- $A$ and $C$ (via Pythagoras, Prop.~1.47, showing $F$ inside the circle), then Euclid's Prop.~2.6
-- gives the rectangle identity.
theorem helper_3_36_step20 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : |(a─f)| = |(f─c)|)
    (h2 : e.isCentre ABC) (h3 : a.onCircle ABC) (h4 : c.onCircle ABC)
    (h6 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
    (h7 : a.onLine DA) (h9 : f.onLine DA) (h10 : d.onLine DA)
    (h11 : between d c a)
    (h12 : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  have hoff : ¬e.onLine DA := fun he => h6 ⟨e, h2, he⟩
  have hc : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have haf : a ≠ f := by
    intro he
    have hcr : ∠ c:f:e = ∟ := h12 c hc (fun hcf => hac (he.trans hcf.symm))
    euclid_apply (line_from_points c f) as CF
    euclid_apply (line_from_points f e) as FE0
    euclid_apply (line_from_points c e) as CE0
    euclid_apply (Elements.Book1.proposition_47 f c e CF CE0 FE0)
    euclid_finish
  have hra : ∠ a:f:e = ∟ := h12 a h7 haf
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points a e) as AE
  euclid_apply (Elements.Book1.proposition_47 f a e AF AE FE)
  have hbtw : between a f c := by euclid_finish
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
