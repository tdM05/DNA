import SystemE
import Book2.Prop04.Main

namespace Elements.Book2

-- The straight-line $CD$ (through $C$, $A$, $D$) has been cut, at random, at point $A$
-- (i.e. $A$ lies between $D$ and $C$). By Prop.~2.4 the square on $DC$ equals the (sum of the)
-- squares on $CA$ and $AD$ and twice the rectangle contained by $CA$ and $AD$.
theorem helper_2_12_step1 (a c d : Point) (CA : Line)
    (h1 : d.onLine CA) (h2 : c.onLine CA) (h3 : between d a c) :
    |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (proposition_4 d c a CA)
  euclid_finish

end Elements.Book2
