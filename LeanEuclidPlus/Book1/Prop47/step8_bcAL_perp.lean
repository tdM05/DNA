import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_bcAL_perp
    (a b c d m : Point) (AL BD BC : Line)
    (haAL : a.onLine AL) (hmAL : m.onLine AL)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hmBC : m.onLine BC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hALBD : ¬AL.intersectsLine BD) (hcbd : ∠ c:b:d = ∟)
    (hdaBC : ¬d.sameSide a BC) (hdoffBC : ¬d.onLine BC)
    (haoffBC : ¬a.onLine BC) (haoffBD : ¬a.onLine BD)
    (ham : a ≠ m) (hmb : m ≠ b) (hbd : b ≠ d) (hcb : c ≠ b) :
    ∠ a:m:b = ∟ := by
  euclid_apply (proposition_29''' a d m b AL BD BC)
  have hmbd : ∠ m:b:d = ∟ := by
    by_cases h : between m b c
    · euclid_finish
    · euclid_apply (equal_angles b m c d d BC BD)
      euclid_finish
  euclid_finish

end Elements.Book1
