import SystemE
import Book3.Prop33.hafg_btw
import Book3.Prop33.hafg_ray
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hafg
    (a b f g g0 : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_g_FG : g.onLine FG) (h_gf : g ≠ f) :
    ∠ a:f:g = ∟ := by
  by_cases hbtw : between g0 f g
  · have hafg_btw : ∠ a:f:g = ∟ := by euclid_apply (helper_3_33_hafg_btw a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g ≠ f; assumption)) (by euclid_assumption "" (show between g0 f g; assumption)))
    exact hafg_btw
  · have hafg_ray : ∠ a:f:g = ∟ := by euclid_apply (helper_3_33_hafg_ray a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g ≠ f; assumption)) (by euclid_assumption "" (show ¬ between g0 f g; assumption)))
    exact hafg_ray

end Elements.Book3
