import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- the (square) on ED is equal to the (sum of the squares) on DF and FE [Prop.~1.47]:
-- triangle EFD is right-angled at F, so ED² = DF² + FE².  The right angle at F for D follows
-- from ∠ EFC = ∟ since D and C lie on the same ray out of F (order d, c, f, a on line AC).
theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : ∠ e:f:c = ∟)
    (h2 : a.onLine DA) (h4 : d.onLine DA) (h5 : f.onLine DA)
    (h6 : between d c a)
    (h8 : e.isCentre ABC) (h9 : e.onLine EF) (h10 : f.onLine EF)
    (h11 : ¬ e.onLine DA) :
    |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hbtw : between a f c := by euclid_finish
  have hright : ∠ e:f:d = ∟ := by euclid_finish
  euclid_apply (line_from_points e d) as ED
  euclid_apply (Elements.Book1.proposition_47 f e d EF ED DA)
  euclid_finish

end Elements.Book3
