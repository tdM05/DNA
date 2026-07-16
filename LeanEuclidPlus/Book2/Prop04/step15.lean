import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step15 (a b c d e g k : Point) (AB CF AD BD BE DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hg_hk : g.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD))
    : ∠ k:b:c = ∟ := by
  have step15_bke : between b k e := by sorry
  euclid_finish

end Elements.Book2
