import SystemE
import Book1.Prop43.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step25 (a b c d e f g h k : Point) (AB CF AD BD BE DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF) (hf_cf : f.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (hk_be : k.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK) (hk_hk : k.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟)
    (had_len : |(a─d)| = |(a─b)|) (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hAD_BE : ¬(AD.intersectsLine BE))
    (hassump1 : ¬(CF.intersectsLine AD)) (hCF_BE : ¬(CF.intersectsLine BE))
    : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ g:k:e + Triangle.area △ g:e:f := by
  have step23_acgh : formParallelogram a c h g AB HK AD CF := by sorry
  have step25_gkef : formParallelogram g k f e HK DE CF BE := by sorry
  have step25_adeb : formParallelogram b e a d BE AD AB DE := by sorry
  have step25_bkcg : formParallelogram b k c g BE CF AB HK := by sorry
  have step25_gfhd : formParallelogram g f h d CF AD HK DE := by sorry
  have step15_bke : between b k e := by sorry
  have step25_lhs : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ c:a:h + Triangle.area △ c:h:g := by sorry
  have step25_rhs : Triangle.area △ g:k:e + Triangle.area △ g:e:f =
      Triangle.area △ k:g:f + Triangle.area △ k:f:e := by sorry
  euclid_apply (Elements.Book1.proposition_43 b a d e c f h k g BE AD AB DE BD CF HK)
  euclid_finish

end Elements.Book2
