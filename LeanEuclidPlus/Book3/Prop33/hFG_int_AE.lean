import SystemE
import Book3.Prop33.hABAE
import Book3.Prop33.hpfa
import Book3.Prop33.hfaq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hFG_int_AE
    (a b c₁ c c₂ d e0 f g0 : Point) (AB AD AE FG : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_afb : between a f b) (h_afeq : |(a─f)| = |(f─b)|)
    (h_g0_AB : ¬ g0.onLine AB)
    (h_afg0 : ∠ a:f:g0 = ∟)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (h_da : d ≠ a) (hne : ∠ c₁:c:c₂ ≠ ∟)
    (hpos : 0 < ∠ c₁:c:c₂) (hlt : ∠ c₁:c:c₂ < ∟ + ∟) :
    FG.intersectsLine AE := by
  have hABFG : AB ≠ FG := by euclid_finish
  have hABAE : AB ≠ AE := by euclid_apply (helper_3_33_hABAE a b c₁ c c₂ d e0 AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  euclid_apply (intersection_lines_common_point a AD AE)
  euclid_apply (intersection_lines_common_point f AB FG)
  -- q on AE, on the same side of AD as b  ⟹  ∠ f:a:q is acute
  euclid_apply (point_on_line_same_side AD AE b) as q
  have hqAB : ¬ q.onLine AB := by euclid_finish
  -- p on FG, on the same side of AB as q
  euclid_apply (point_on_line_same_side AB FG q) as p
  -- ∠ p:f:a is a right angle (FG ⊥ AB at f); ∠ f:a:q is acute (q on b-side of AD, AE ⊥ AD)
  have hpfa : ∠ a:f:p = ∟ := by euclid_apply (helper_3_33_hpfa a b f g0 p q AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show p.onLine FG; assumption)) (by euclid_assumption "" (show p.sameSide q AB; assumption)))
  have hfaq : ∠ f:a:q < ∟ := by euclid_apply (helper_3_33_hfaq a b c₁ c c₂ d e0 f q AB AD AE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show q.onLine AE; assumption)) (by euclid_assumption "" (show q.sameSide b AD; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)))
  -- parallel-postulate axiom: right + acute < two right angles ⟹ FG and AE meet
  euclid_apply (lines_intersect p f a q FG AB AE) as e
  euclid_finish

end Elements.Book3
