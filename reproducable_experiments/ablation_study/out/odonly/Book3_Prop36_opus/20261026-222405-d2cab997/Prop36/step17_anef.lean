import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_anef (a c e f : Point) (ABC : Circle) (DA EF EC : Line)
    (hcda : c.onLine DA) (hfDA : f.onLine DA) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (heEC : e.onLine EC) (hcEC : c.onLine EC)
    (hacirc : a.onCircle ABC) (hccirc : c.onCircle ABC) (hecentre : e.isCentre ABC)
    (hennotDA : ¬ e.onLine DA) (hac : a ≠ c)
    (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    a ≠ f := by
  intro heq
  have hcf : c ≠ f := by rw [← heq]; exact fun h => hac h.symm
  have hrc : ∠ c:f:e = ∟ := hperp_all c hcda hcf
  euclid_apply (proposition_47 f c e DA EC EF)
  euclid_finish

end Elements.Book3
