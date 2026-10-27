import SystemE
import Book1.Prop30.Main
import Book1Variants.Prop34

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step17 (f g h k l m : Point) (FG KH HM GL FK LM GH : Line)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))   -- "$FK$ is equal and parallel to $HG$"
  (hassump2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))   -- "$HG$ to $ML$"
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH)
  (hniFGKH : ¬FG.intersectsLine KH) (hniFKGH : ¬FK.intersectsLine GH)
  (hhHM : h.onLine HM) (hmHM : m.onLine HM)
  (hgGL : g.onLine GL) (hlGL : l.onLine GL)
  (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
  (hsameLM : h.sameSide g LM)
  (hniHMGL : ¬HM.intersectsLine GL) (hniGHLM : ¬GH.intersectsLine LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  obtain ⟨hopp, _⟩ := hstep9
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_apply (proposition_34' h m g l HM GL GH LM)
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1
