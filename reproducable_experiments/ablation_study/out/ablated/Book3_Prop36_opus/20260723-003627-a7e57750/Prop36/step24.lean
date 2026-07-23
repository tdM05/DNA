import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- $DFE$ is a right-angle (same perpendicular $EF$, now with $D$ on line $DA$ beyond the chord), so
-- Pythagoras (Prop.~1.47) on triangle $FED$ (right-angle at $F$) gives the square on $ED$ as the
-- sum of the squares on $DF$ and $FE$.
theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA : Line)
    (h1 : ∠ e:f:c = ∟)
    (h3 : e.isCentre ABC)
    (h6 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
    (h7 : a.onLine DA) (h9 : f.onLine DA) (hda : d.onLine DA)
    (h10 : between d c a) :
    |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hoff : ¬e.onLine DA := fun he => h6 ⟨e, h3, he⟩
  have hc : c.onLine DA := by euclid_finish
  have hdf : d ≠ f := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  have hefd : ∠ e:f:d = ∟ := by euclid_finish
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points d e) as DE
  euclid_apply (Elements.Book1.proposition_47 f e d FE DE DA)
  euclid_finish

end Elements.Book3
