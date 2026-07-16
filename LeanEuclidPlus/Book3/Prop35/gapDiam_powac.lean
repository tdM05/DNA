import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_35_gapDiam_powac (a c e f : Point) (ABCD : Circle) (AC : Line)
  (ha : a.onCircle ABCD) (hc : c.onCircle ABCD) (hbet1 : between a e c)
  (hfc : f.isCentre ABCD) (haAC : a.onLine AC) (hcAC : c.onLine AC)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by
  by_cases hf_ac : f.onLine AC
  · -- $AC$ passes through the centre: $F$ itself is the midpoint of the chord.
    have gapDiam_powac_diam : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by sorry
    exact gapDiam_powac_diam
  · -- $AC$ not through the centre: drop the perpendicular from $F$ to $AC$.
    have gapDiam_powac_perp : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by sorry
    exact gapDiam_powac_perp

end Elements.Book3
