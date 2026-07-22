import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG HM KH GH : Line)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hmHM : m.onLine HM) (hhHM : h.onLine HM)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hss : f.sameSide k GH) (hkGH : ¬ k.onLine GH) (hmGH : ¬ m.onLine GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hstep10 : KH = HM)
    (hassump1 : ¬(FG.intersectsLine KH)) :
    ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1
