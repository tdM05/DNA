import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step24 (a b c d e f g h k : Point) (AB CF AD BD DE HK : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hacb : between a c b) (hab : a ≠ b)
    (hc_cf : c.onLine CF) (hg_cf : g.onLine CF) (hf_cf : f.onLine CF)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD) (hh_ad : h.onLine AD)
    (hb_bd : b.onLine BD) (hg_bd : g.onLine BD) (hd_bd : d.onLine BD) (hbd : b ≠ d)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hg_hk : g.onLine HK) (hh_hk : h.onLine HK)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hHK_AB : ¬(HK.intersectsLine AB)) (hDE_AB : ¬(DE.intersectsLine AB))
    (hassump1 : ¬(CF.intersectsLine AD))
    (hstep21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)
    (hstep23 : |(h─g)| = |(a─c)|)
    (hstep22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)))
    : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by
  obtain ⟨⟨he1, he2, he3⟩, hr1, hr2, hr3, hr4⟩ := hstep22
  have step22_par : formParallelogram h g d f HK DE AD CF := by sorry
  have hrect : Triangle.area △ h:d:f + Triangle.area △ h:g:f = |(h─g)| * |(h─d)| := by
    euclid_apply (rectangle_area h g d f HK DE AD CF)
    euclid_finish
  have hhd_hg : |(h─d)| = |(h─g)| := by euclid_finish
  have hprod : |(h─g)| * |(h─d)| = |(a─c)| * |(a─c)| := by rw [hhd_hg, hstep23]
  rw [hprod] at hrect
  refine ⟨?_, hstep21⟩
  euclid_finish

end Elements.Book2
