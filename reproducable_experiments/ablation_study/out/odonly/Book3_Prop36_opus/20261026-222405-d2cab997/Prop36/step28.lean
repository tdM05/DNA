import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step28 (e b d : Point) (ABC : Circle) (EB ED DB : Line)
  (hbEB : b.onLine EB) (heEB : e.onLine EB) (heED : e.onLine ED) (hdED : d.onLine ED)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hbcirc : b.onCircle ABC) (hecentre : e.isCentre ABC)
  (hdnotin : ¬ d.insideCircle ABC) (hdnotcirc : ¬ d.onCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:b:d = ∟)   -- "$EBD$ (is) a right-angle"
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  euclid_apply (proposition_47 b e d EB ED DB)
  have hs : |(d─b)| = |(b─d)| := by euclid_finish
  rw [hs]
  euclid_finish

end Elements.Book3
