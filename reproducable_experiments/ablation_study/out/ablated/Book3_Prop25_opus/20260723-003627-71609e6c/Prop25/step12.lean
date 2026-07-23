import SystemE
import Book1.Prop04.Main

namespace Elements.Book3

open Elements.Book1

-- The base AE equals the base CE [Prop.~1.4]: triangles ADE and CDE have AD = CD, side DE common,
-- and the included angles ∠ADE = ∠CDE, so by SAS the bases AE and CE are equal.
theorem helper_3_25_step12 (a c d e : Point) (AC AG DB EC : Line)
    (h1 : |(a─d)| = |(c─d)|) (h2 : ∠ a:d:e = ∠ c:d:e)
    (h3 : a.onLine AC) (h4 : c.onLine AC) (h5 : d.onLine AC)
    (h6 : a.onLine AG) (h7 : e.onLine AG)
    (h8 : d.onLine DB) (h9 : e.onLine DB)
    (h10 : e.onLine EC) (h11 : c.onLine EC)
    (h12 : between a d c) (h13 : ¬e.onLine AC) :
    |(a─e)| = |(c─e)| := by
  euclid_apply (proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3
