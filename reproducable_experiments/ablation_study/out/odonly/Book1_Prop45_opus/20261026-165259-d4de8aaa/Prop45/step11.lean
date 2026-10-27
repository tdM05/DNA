import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step11 (f g h k m : Point) (FG KH HM GH : Line)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ¬(FG.intersectsLine KH))   -- "the straight-line $HG$ falls across the parallels $KM$ and $FG$"
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH)
  (hhHM : h.onLine HM) (hmHM : m.onLine HM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  (hstep10 : KH = HM)
  : ∠ m:h:g = ∠ h:g:f := by
  obtain ⟨hopp, _⟩ := hstep9
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1
