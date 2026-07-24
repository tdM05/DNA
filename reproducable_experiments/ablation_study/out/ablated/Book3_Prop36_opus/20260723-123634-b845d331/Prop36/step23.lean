import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- the (square) on EC is equal to the (sum of the squares) on CF and FE [Prop.~1.47]:
-- triangle EFC is right-angled at F (∠ e:f:c = ∟), so EC² = FC² + EF².
-- (c.onLine DA and c ≠ f are derived internally: c is between d and a on DA, f off e's line.)
theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : ∠ e:f:c = ∟)
    (h2 : c.onCircle ABC) (h3 : a.onLine DA) (h3b : d.onLine DA) (h4 : f.onLine DA)
    (hbtw : between d c a)
    (h5 : e.isCentre ABC) (h6 : e.onLine EF) (h7 : f.onLine EF)
    (h8 : ¬ e.onLine DA) :
    |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hcDA : c.onLine DA := by euclid_finish
  euclid_apply (line_from_points e c) as EC
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  euclid_finish

end Elements.Book3
