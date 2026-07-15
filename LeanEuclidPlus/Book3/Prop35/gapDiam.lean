import SystemE
import Mathlib.Tactic.Linarith

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_35_gapDiam (a b c d e f : Point) (ABCD : Circle) (AC BD : Line)
  (ha : a.onCircle ABCD) (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hd : d.onCircle ABCD)
  (hbet1 : between a e c) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  -- power of the point E: |XE|·|EY| + |FE|² = |FX|² (= r²) for each chord, whether or not it is a diameter
  have gapDiam_powac : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by sorry
  have gapDiam_powbd : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by sorry
  have hrad : |(f─a)| = |(f─b)| := by euclid_finish
  have hrad2 : |(f─a)| * |(f─a)| = |(f─b)| * |(f─b)| := by rw [hrad]
  linarith [gapDiam_powac, gapDiam_powbd, hrad2]

end Elements.Book3
