import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step16 (f g h k l m : Point) (FG GL GH LM : Line)
  (hhGH : h.onLine GH) (hgGH : g.onLine GH) (hgh : g ≠ h)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hgGL : g.onLine GL) (hlGL : l.onLine GL)
  (hsame : f.sameSide k GH) (hsameLM : h.sameSide g LM)
  (hlLM : l.onLine LM) (hmLM : m.onLine LM) (hni : ¬GH.intersectsLine LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  (hstep15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟)
  : FG = GL := by
  obtain ⟨hopp, _⟩ := hstep9
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1
