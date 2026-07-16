import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step22 (a b c d e f g h : Point) (AB CF AD BD BE DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF) (hf_cf : f.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (hang_e : ∠ a:b:e = ∟) (hang_de : ∠ a:d:e = ∟)
    (had_len : |(a─d)| = |(a─b)|) (hbe_len : |(b─e)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD)) (hCF_BE : ¬(CF.intersectsLine BE))
    (hstep6 : ∠ a:d:b = ∠ a:b:d)
    : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)) := by
  have step22_par : formParallelogram h g d f HK DE AD CF := by sorry
  have step22_hdhg : |(h─d)| = |(h─g)| := by sorry
  have step22_ra : (∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟) := by sorry
  have hsides : |(h─g)| = |(d─f)| ∧ |(h─d)| = |(g─f)| := by
    euclid_apply (Elements.Book1.proposition_34' h g d f HK DE AD CF)
    euclid_finish
  refine ⟨⟨?_, ?_, ?_⟩, step22_ra⟩ <;> euclid_finish

end Elements.Book2
