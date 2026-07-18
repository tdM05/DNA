import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hafg_ray
    (a b f g g0 : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_g_FG : g.onLine FG) (h_gf : g ≠ f) (h_ray : ¬ between g0 f g) :
    ∠ a:f:g = ∟ := by
  have haf : a ≠ f := by euclid_finish
  have hg0f : g0 ≠ f := by euclid_finish
  euclid_apply (equal_angles f a a g g0 AB FG)
  euclid_finish

end Elements.Book3
