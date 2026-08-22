import AxiomSoundnessProofs.Interpretation.CircularSegments

/-!
# ℝ² interpretation — relations

Mirrors `SystemE/Theory/Relations.lean`.  One `def` per `opaque` relation there.
(The `abbrev`/`def` relations in System E — `distinctPointsOnLine`, `opposingSides`,
`outsideCircle`, `formTriangle`, `formCircularSegment`, `coincides`, … — are TRANSPARENT: they
unfold to these primitives, so they get no separate interpretation.  We still give the couple
that our current proofs consume directly.)
-/

namespace RInterp

/-- **`Point.onLine`** `p L` ↦ `ℓ_L(p) = 0`. -/
def onLine (p : Pt) (L : Line) : Prop := ℓ L p = 0

/-- **`Point.sameSide`** `p q L` ↦ `ℓ_L(p)·ℓ_L(q) > 0` (strictly same sign, so both off `L`). -/
def sameSide (p q : Pt) (L : Line) : Prop := ℓ L p * ℓ L q > 0

/-- **`between`** `a b c` ↦ `b` strictly between `a` and `c`: `b = a + t·(c − a)` for some
`t ∈ (0,1)`.  (Collinearity is implied by the parametric form, so it needs no separate conjunct.) -/
def between (a b c : Pt) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ b = a + t • (c - a)

/-- **`Point.onCircle`** `p γ` ↦ `‖p − c‖² = r²`. -/
def onCircle (p : Pt) (γ : Circle) : Prop := dot (p - γ.c) (p - γ.c) = γ.r^2

/-- **`Point.insideCircle`** `p γ` ↦ `‖p − c‖² < r²`. -/
def insideCircle (p : Pt) (γ : Circle) : Prop := dot (p - γ.c) (p - γ.c) < γ.r^2

/-- **`Point.isCentre`** `p γ` ↦ `p = c`. -/
def isCentre (p : Pt) (γ : Circle) : Prop := p = γ.c

/-- **`Line.intersectsLine`** `L M` ↦ some point lies on both. -/
def Line.intersectsLine (L M : Line) : Prop := ∃ p : Pt, onLine p L ∧ onLine p M

/-- **`Line.intersectsCircle`** `L γ` ↦ some point lies on `L` and on `γ`. -/
def Line.intersectsCircle (L : Line) (γ : Circle) : Prop := ∃ p : Pt, onLine p L ∧ onCircle p γ

/-- **`Circle.intersectsCircle`** `α β` ↦ some point lies on both circles. -/
def Circle.intersectsCircle (α β : Circle) : Prop := ∃ p : Pt, onCircle p α ∧ onCircle p β

/-- **`distinctPointsOnLine`** — System E's transparent `abbrev`, given here for proofs to use. -/
def distinctPointsOnLine (p q : Pt) (L : Line) : Prop := onLine p L ∧ onLine q L ∧ p ≠ q

/-- **`CircularSegment.inside`** `s t` (III.24 "falls inside it") ↦ `s`'s region is enclosed in
`t`'s: `s.region ⊂ t.region` (proper subset). -/
def CircularSegment.inside (s t : CircularSegment) : Prop := s.region ⊂ t.region

/-- **`CircularSegment.outside`** `s t` (III.24 "outside it") ↦ the MIRROR of `inside`: `t`'s region
is enclosed in `s`'s, `t.region ⊂ s.region`.  Then III.24's trichotomy
`inside ∨ outside ∨ (¬inside ∧ ¬outside)` reads as: `s ⊂ t` / `t ⊂ s` / incomparable (the "miss",
where the arcs cross) — matching `Book3/Prop24/Main.lean` line 115.  NOT `¬inside`. -/
def CircularSegment.outside (s t : CircularSegment) : Prop := t.region ⊂ s.region

end RInterp
