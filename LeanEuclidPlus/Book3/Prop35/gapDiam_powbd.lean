import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_35_gapDiam_powbd (b d e f : Point) (ABCD : Circle) (BD : Line)
  (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  by_cases hf_bd : f.onLine BD
  · -- $BD$ passes through the centre: $F$ itself is the midpoint of the chord.
    have gapDiam_powbd_diam : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by sorry
    exact gapDiam_powbd_diam
  · -- $BD$ not through the centre: drop the perpendicular from $F$ to $BD$.
    have gapDiam_powbd_perp : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by sorry
    exact gapDiam_powbd_perp

end Elements.Book3
