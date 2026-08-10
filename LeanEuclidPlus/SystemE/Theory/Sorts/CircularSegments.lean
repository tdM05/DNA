import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

/--
A circular segment (Euclid's "segment of a circle", Book III Def. 6: "the figure contained
by a straight-line and a circumference of a circle") is the 2-D REGION capped between a chord
and one of the two arcs it cuts off. It is NOT the straight-line `Segment` of `Sorts/Segments`
(that is a 1-D chord, with a `length`); this is a plane figure, so it carries an AREA — the
same magnitude kind as `Triangle.area`.

Like `Arc`, and for the same reason, it is given by THREE points: endpoints `a`, `c` and a
point `b` on the arc between them, which disambiguates WHICH of the two segments on chord
`(a─c)` is meant. Written `⌓ a:b:c` (the segment on chord a-c, bulging through b).
-/
inductive CircularSegment
| ofPoints (a b c : Point)

namespace CircularSegment

opaque area : CircularSegment → ℝ

instance : Coe CircularSegment ℝ := ⟨area⟩

instance : LT CircularSegment := ⟨fun a b => area a < area b⟩

end CircularSegment

notation:71 "⌓" a ":" b ":" c:72 => CircularSegment.area (CircularSegment.ofPoints a b c)

open Lean PrettyPrinter

@[app_unexpander CircularSegment.area]
def unexpand_area : Unexpander
| `($_ (`CircularSegment.ofPoints $a:ident $b:ident $c:ident)) => `(⌓ $a:ident : $b:ident : $c:ident)
| _ => throw ()
