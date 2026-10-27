import SystemE
import Book1.Prop45.step20_fklm
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20 (f g h k l m : Point) (FG KH HM FK LM GL GH : Line)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hlGL : l.onLine GL) (hstep16 : FG = GL)
  (hkKH : k.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hlLM : l.onLine LM) (hmLM : m.onLine LM) (hml : m ≠ l)
  (hniFGKH : ¬FG.intersectsLine KH)
  (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
  (hgGH : g.onLine GH) (hhGH : h.onLine GH)
  (hniLMGH : ¬GH.intersectsLine LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : formParallelogram f l k m FG KH FK LM := by
  obtain ⟨hlen, hpar⟩ := hstep17
  obtain ⟨hopp, _⟩ := hstep9
  have step20_fklm : f.sameSide k LM := by euclid_apply (helper_1_45_step20_fklm f k m FK LM GH (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))
  euclid_finish

end Elements.Book1
