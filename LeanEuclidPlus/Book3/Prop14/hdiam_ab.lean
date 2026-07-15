import SystemE
import Mathlib.Tactic.Linarith

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_14_hdiam_ab
    (a b e : Point) (ABDC : Circle) (AB : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hab : a ≠ b) :
    |(a─b)| = |(a─e)| + |(a─e)| := by
  have hbet : between a e b := by euclid_finish
  have hsum : |(a─e)| + |(e─b)| = |(a─b)| := between_if a e b hbet
  have hrad : |(e─b)| = |(a─e)| := by euclid_finish
  linarith

end Elements.Book3
