import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step24
  (a c d e f : Point) (ABC : Circle) (DA EF ED : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (he : e.isCentre ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (step17 : |(a─f)| = |(f─c)|)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hnoteDA : ¬e.onLine DA := fun h => hnotthrough ⟨e, he, h⟩
  have hdf : d ≠ f := by euclid_finish
  have hperpd : ∠ d:f:e = ∟ := hperp d hdDA hdf
  euclid_apply (Elements.Book1.proposition_47 f e d EF ED DA)
  rw [segment_symmetric d f, segment_symmetric f e]
  linarith

end Elements.Book3
