import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA EF ED : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA) (hbdca : between d c a)
  (hfEF : f.onLine EF) (heEF : e.onLine EF) (heED : e.onLine ED) (hdED : d.onLine ED)
  (hecentre : e.isCentre ABC) (hhalf : |(a─f)| = |(f─c)|)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hennotDA : ¬ e.onLine DA := fun h => hnotthrough ⟨e, hecentre, h⟩
  have hac : a ≠ c := by euclid_finish
  have hbafc : between a f c := by euclid_finish
  have hdf : d ≠ f := by euclid_finish
  have hefd : ∠ d:f:e = ∟ := hperp_all d hdDA hdf
  euclid_apply (proposition_47 f e d EF ED DA)
  have hs1 : |(d─f)| = |(f─d)| := by euclid_finish
  have hs2 : |(f─e)| = |(e─f)| := by euclid_finish
  rw [hs1, hs2]
  euclid_finish

end Elements.Book3
