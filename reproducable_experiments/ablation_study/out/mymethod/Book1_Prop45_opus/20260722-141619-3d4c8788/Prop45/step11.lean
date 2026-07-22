import SystemE
import Book1Variants.Prop29

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG KH HM GH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG)
    (h3 : k.onLine KH) (h4 : h.onLine KH)
    (h5 : m.onLine HM) (h6 : h.onLine HM)
    (h7 : g.onLine GH) (h8 : h.onLine GH) (h9 : g ≠ h)
    (h10 : f.sameSide k GH) (h11 : ¬m.sameSide k GH) (h12 : ¬m.onLine GH)
    (hstep10 : KH = HM)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ¬(FG.intersectsLine KH))   -- "the straight-line $HG$ falls across the parallels $KM$ and $FG$"
    : ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG KH GH)
  euclid_finish

end Elements.Book1
