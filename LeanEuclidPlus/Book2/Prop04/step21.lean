import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step21 (a b c d e g k : Point) (AB CF AD BD BE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE) (he_be : e.onLine BE)
    (hg_hk : g.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟) (had_len : |(a─d)| = |(a─b)|)
    (hbe_len : |(b─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hAD_BE : ¬(AD.intersectsLine BE))
    (hassump1 : ¬(CF.intersectsLine AD))
    (hstep8 : |(b─c)| = |(c─g)|) (hstep17 : (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟))
    : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)| := by
  have step9_par : formParallelogram c b g k AB HK CF BE := by sorry
  have hrect : Triangle.area △ c:g:k + Triangle.area △ c:b:k = |(c─b)| * |(c─g)| := by
    euclid_apply (rectangle_area c b g k AB HK CF BE)
    euclid_finish
  have hlen : |(c─g)| = |(c─b)| := by euclid_finish
  rw [hlen] at hrect
  euclid_finish

end Elements.Book2
