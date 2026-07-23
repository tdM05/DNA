import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- $EFC$ is a right-angle (the perpendicular $EF$ meets the chord $AC$ at its foot $F$).  With
-- $|AF| = |FC|$ and $A, F, C$ collinear ($A \ne C$), $F$ is the midpoint, hence distinct from $C$,
-- and $E$ (the off-line centre) is distinct from both.  Pythagoras (Prop.~1.47) on triangle $FEC$
-- (right-angle at $F$) then gives the square on $EC$ as the sum of the squares on $CF$ and $FE$.
theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA : Line)
    (h1 : ∠ e:f:c = ∟)
    (h2 : |(a─f)| = |(f─c)|)
    (h3 : e.isCentre ABC) (h4 : a.onCircle ABC) (h5 : c.onCircle ABC)
    (h6 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
    (h7 : a.onLine DA) (h9 : f.onLine DA)
    (h10 : between d c a) :
    |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hoff : ¬e.onLine DA := fun he => h6 ⟨e, h3, he⟩
  have hc : c.onLine DA := by euclid_finish
  have hfc : f ≠ c := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  have hec : e ≠ c := by euclid_finish
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (Elements.Book1.proposition_47 f e c FE CE DA)
  euclid_finish

end Elements.Book3
