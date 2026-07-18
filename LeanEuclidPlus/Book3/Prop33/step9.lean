import SystemE
import Book1.Prop04.Main
import Book3.Prop33.hABAE
import Book3.Prop33.hga
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step9
    (a b c₁ c c₂ d e0 f g g0 : Point) (AB AD AE FG GB : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_afb : between a f b) (h_afeq : |(a─f)| = |(f─b)|)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG) (h_g_FG : g.onLine FG)
    (h_g_AE : g.onLine AE) (h_g_GB : g.onLine GB) (h_b_GB : b.onLine GB)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (h_da : d ≠ a) (hne : ∠ c₁:c:c₂ ≠ ∟)
    (h_afg : ∠ a:f:g = ∟) (h_step8 : ∠ a:f:g = ∠ b:f:g) :
    |(a─g)| = |(b─g)| := by
  have hABAE : AB ≠ AE := by euclid_apply (helper_3_33_hABAE a b c₁ c c₂ d e0 AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hga : g ≠ a := by euclid_apply (helper_3_33_hga a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
  have hgAB : ¬ g.onLine AB := by
    intro hg
    euclid_apply (two_points_determine_line g a AB AE)
    exact hABAE (by euclid_finish)
  euclid_apply (line_from_points a g) as AG
  euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AG FG AB GB FG)
  euclid_finish

end Elements.Book3
