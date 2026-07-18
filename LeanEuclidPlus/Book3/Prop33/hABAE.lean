import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hABAE
    (a b c₁ c c₂ d e0 : Point) (AB AD AE : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (h_da : d ≠ a) (hne : ∠ c₁:c:c₂ ≠ ∟) :
    AB ≠ AE := by
  intro heq
  have hb_AE : b.onLine AE := heq ▸ h_b_AB
  have he0a : e0 ≠ a := by euclid_finish
  have hdab_right : ∠ d:a:b = ∟ := by
    by_cases hbtw : between b a e0
    · euclid_apply (perpendicular_onlyif e0 b a d AE)
      euclid_finish
    · euclid_apply (equal_angles a d d b e0 AD AE)
      euclid_finish
  rw [h_dab] at hdab_right
  exact hne hdab_right

end Elements.Book3
