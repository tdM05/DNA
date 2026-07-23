import SystemE
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace Elements.Book2

theorem helper_11_golden (A M E Q F AH BH : ℝ)
    (hA : A = M + M) (hE : E = M) (hpy : Q * Q = E * E + A * A)
    (hQ : Q = E + F) (hAH : AH = F) (hBH : A = AH + BH) :
    A * BH = AH * AH := by
  subst hE hQ hA hAH
  linear_combination (-2 * E) * hBH - hpy

theorem helper_11_af_lt_ab (A M E Q F : ℝ)
    (hM : M > 0) (hA : A = M + M) (hE : E = M)
    (hpy : Q * Q = E * E + A * A) (hQ : Q = E + F)
    (hQnn : Q ≥ 0) :
    F < A := by
  subst hE hA
  nlinarith [hpy, hQnn, hM, hQ]

end Elements.Book2
