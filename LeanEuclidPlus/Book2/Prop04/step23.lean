import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step23 (a b c d g h : Point) (AB CF AD BD HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hassump1 : ¬(CF.intersectsLine AD))
    : |(h─g)| = |(a─c)| := by
  have step23_acgh : formParallelogram a c h g AB HK AD CF := by sorry
  euclid_apply (Elements.Book1.proposition_34' a c h g AB HK AD CF)
  euclid_finish

end Elements.Book2
