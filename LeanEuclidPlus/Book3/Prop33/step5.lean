import SystemE
import Book3.Prop33.hABAE
import Book3.Prop33.hafg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step5
    (a b c₁ c c₂ d e0 f g g0 : Point) (AB AD AE FG : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG) (h_g_FG : g.onLine FG)
    (h_g_AE : g.onLine AE)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (h_da : d ≠ a) (hne : ∠ c₁:c:c₂ ≠ ∟) :
    ∠ a:f:g = ∟ := by
  have hABAE : AB ≠ AE := by euclid_apply (helper_3_33_hABAE a b c₁ c c₂ d e0 AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hgf : g ≠ f := by
    intro heq
    have hf_AE : f.onLine AE := heq ▸ h_g_AE
    have hdist : distinctPointsOnLine a f AE := by euclid_finish
    euclid_apply (two_points_determine_line a f AE AB)
    exact hABAE (by euclid_finish)
  have hafg : ∠ a:f:g = ∟ := by euclid_apply (helper_3_33_hafg a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g ≠ f; assumption)))
  exact hafg

end Elements.Book3
