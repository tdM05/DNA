import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hpfa
    (a b f g0 p q : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_p_FG : p.onLine FG) (h_pq : p.sameSide q AB) :
    ∠ a:f:p = ∟ := by
  have haf : a ≠ f := by euclid_finish
  have hf_AB : f.onLine AB := by euclid_finish
  have hpf : p ≠ f := by euclid_finish
  have hg0f : g0 ≠ f := by euclid_finish
  by_cases hbtw : between g0 f p
  · -- opposite rays: ∠a:f:p is the supplement of ∠a:f:g0 = ∟
    euclid_finish
  · -- same ray: ∠a:f:p = ∠a:f:g0 = ∟
    euclid_apply (equal_angles f a a p g0 AB FG)
    euclid_finish

end Elements.Book3
