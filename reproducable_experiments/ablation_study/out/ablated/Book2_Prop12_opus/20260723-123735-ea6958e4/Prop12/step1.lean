import SystemE
import Book2.Prop04.Main

namespace Elements.Book2

-- The straight-line $CD$ has been cut, at random, at point $A$ (between d a c),
-- so the square on $DC$ equals the squares on $CA$ and $AD$ plus twice the
-- rectangle contained by $CA$ and $AD$ [Prop.~2.4].
theorem helper_2_12_step1 (a c d : Point) (CA : Line)
    (h1 : between d a c)
    (hd : d.onLine CA) (hc : c.onLine CA) (ha : a.onLine CA) :
    |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  -- Prop.~2.4 applied to $CD$ cut at $A$ gives the identity with the reversed
  -- segment orientations; realign them with the symmetry of segment length.
  euclid_apply (Elements.Book2.proposition_4 d c a CA)
  rw [segment_symmetric c a, segment_symmetric a d]
  linarith [mul_comm (|(a─c)|) (|(d─a)|)]

end Elements.Book2
