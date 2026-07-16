import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step7 (a b c d g : Point) (AB CF AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hassump1 : ¬(CF.intersectsLine AD))
    (hstep5 : ∠ c:g:b = ∠ a:d:b) (hstep6 : ∠ a:d:b = ∠ a:b:d)
    : ∠ c:g:b = ∠ g:b:c := by
  have step5_bgd : between b g d := by sorry
  euclid_finish

end Elements.Book2
