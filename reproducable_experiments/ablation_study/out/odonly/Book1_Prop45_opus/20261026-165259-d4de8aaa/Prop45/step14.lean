import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step14 (g h k l m : Point) (GL HM GH LM : Line)
  (hgGL : g.onLine GL) (hlGL : l.onLine GL)
  (hhHM : h.onLine HM) (hmHM : m.onLine HM)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
  (hsameLM : h.sameSide g LM)
  (hni1 : ¬HM.intersectsLine GL) (hni2 : ¬GH.intersectsLine LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  obtain ⟨hopp, _⟩ := hstep9
  euclid_apply (proposition_29''''' l m g h GL HM GH)
  euclid_finish

end Elements.Book1
