import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step28
  (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (hb : b.onCircle ABC) (he : e.isCentre ABC) (hd_noton : ¬d.onCircle ABC)
  (heEB : e.onLine EB) (hbEB : b.onLine EB)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (hdDB : d.onLine DB) (hbDB : b.onLine DB)
  (hassump1 : ∠ e:b:d = ∟)   -- "$EBD$ (is) a right-angle"
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have hnotbED : ¬b.onLine ED := by euclid_finish
  have htri : formTriangle b e d EB ED DB := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB)
  rw [segment_symmetric d b]
  linarith

end Elements.Book3
