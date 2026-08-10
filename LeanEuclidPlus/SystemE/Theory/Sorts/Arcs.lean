import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

/--
An arc (Euclid's "circumference", περιφέρεια, of a circle) is the piece of a circle's
boundary from one endpoint to another. Written `⌒ a:b:c` (the arc from `a` to `c` through `b`).
-/
inductive Arc
| ofPoints (a b c : Point)

namespace Arc

opaque measure : Arc → ℝ

instance : Coe Arc ℝ := ⟨measure⟩

instance : LT Arc := ⟨fun a b => measure a < measure b⟩

end Arc

notation:71 "⌒" a ":" b ":" c:72 => Arc.measure (Arc.ofPoints a b c)

open Lean PrettyPrinter

@[app_unexpander Arc.measure]
def unexpand_measure : Unexpander
| `($_ (`Arc.ofPoints $a:ident $b:ident $c:ident)) => `(⌒ $a:ident : $b:ident : $c:ident)
| _ => throw ()
