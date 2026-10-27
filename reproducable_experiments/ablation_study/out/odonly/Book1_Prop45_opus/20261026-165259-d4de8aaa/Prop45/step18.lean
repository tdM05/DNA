import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (FG KH HM GL GH LM : Line)
  (hkKH : k.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hfFG : f.onLine FG) (hlGL : l.onLine GL) (hstep16 : FG = GL)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH)
  (hsame : f.sameSide k GH) (hsameLM : h.sameSide g LM)
  (hlLM : l.onLine LM) (hmLM : m.onLine LM) (hniLM : ¬GH.intersectsLine LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  obtain ⟨hopp, _⟩ := hstep9
  euclid_finish

end Elements.Book1
