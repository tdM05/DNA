import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step5 (a b c d g : Point) (AB CF AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hassump1 : ¬(CF.intersectsLine AD))   -- "$CF$ is parallel to $AD$"
    : ∠ c:g:b = ∠ a:d:b := by
  have step5_bgd : between b g d := by sorry
  have step5_ss : c.sameSide a BD := by sorry
  euclid_apply (Elements.Book1.proposition_29'''' c a b g d CF AD BD)
  euclid_finish

end Elements.Book2
