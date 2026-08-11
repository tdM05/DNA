import SystemE.Theory.Sorts

opaque Point.onLine : Point → Line → Prop

@[simp]
abbrev distinctPointsOnLine : Point → Point → Line → Prop := λ P Q L => P.onLine L ∧ Q.onLine L ∧ P ≠ Q

namespace Point

opaque sameSide : Point → Point → Line → Prop

@[simp]
abbrev opposingSides : Point → Point → Line → Prop :=
  λ a b l => ¬ a.onLine l  ∧ ¬ b.onLine l ∧ ¬ sameSide a b l

end Point

opaque collinear (a b c : Point) : Prop



/--
`between x y z` means `y` is between `x` and `z`
-/
opaque between : Point → Point → Point → Prop


namespace Point

opaque onCircle : Point → Circle → Prop

opaque insideCircle : Point → Circle → Prop

@[simp]
abbrev outsideCircle : Point → Circle → Prop :=
λ p c => ¬ p.insideCircle c ∧ ¬ p.onCircle c

opaque isCentre : Point → Circle → Prop

end Point

namespace Line

opaque intersectsLine : Line → Line → Prop

opaque intersectsCircle : Line → Circle → Prop


end Line

namespace Circle

opaque intersectsCircle : Circle → Circle → Prop

end Circle

namespace CircularSegment

/-- `s.inside t`: circular segment `s` lies inside segment `t` (III.24, "it will fall inside it").
The two segments share a chord; `s`'s arc is enclosed by `t`'s arc on the same side. -/
opaque inside : CircularSegment → CircularSegment → Prop

/-- `s.outside t`: circular segment `s` lies outside segment `t` (III.24, "outside it"). Not the
negation of `inside`: III.24's trichotomy also has the "miss"/crossing case, so `outside` is a
distinct primitive, not `¬ inside`. -/
opaque outside : CircularSegment → CircularSegment → Prop

end CircularSegment

@[simp]
abbrev formTriangle (a b c : Point) (AB BC CA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧
  b.onLine BC ∧ c.onLine BC ∧ c.onLine CA ∧ a.onLine CA ∧
  AB ≠ BC ∧ BC ≠ CA ∧ CA ≠ AB

@[simp]
abbrev formRectilinearAngle (a b c : Point) (AB BC : Line) :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC

@[simp]
abbrev formParallelogram (a b c d : Point) (AB CD AC BD : Line) : Prop :=
    a.onLine AB ∧ b.onLine AB ∧ c.onLine CD ∧ d.onLine CD ∧ a.onLine AC ∧ c.onLine AC ∧ distinctPointsOnLine b d BD ∧
    (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ ¬(AC.intersectsLine BD)
