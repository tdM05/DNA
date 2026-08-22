import Mathlib.Data.Real.Basic

/-!
# ℝ² interpretation — primitive sorts

Mirrors `SystemE/Theory/Sorts/Primitives.lean`.  One object per primitive sort.
Each declaration here IS the interpretation `I(sort)` of a System-E carrier; nothing else.
-/

namespace RInterp

/-- **`Point`** ↦ `ℝ × ℝ`. -/
abbrev Pt := ℝ × ℝ

/-- **`Line`** ↦ an affine form `a·x + b·y = c` with `(a,b) ≠ 0`. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nondeg : a ≠ 0 ∨ b ≠ 0

/-- **`Circle`** ↦ centre `c : Pt` (a point of ℝ²) and radius `r > 0`. -/
structure Circle where
  c : Pt
  r : ℝ
  pos : r > 0

end RInterp
