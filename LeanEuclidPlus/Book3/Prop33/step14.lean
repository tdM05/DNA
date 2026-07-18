import SystemE
import Book3.Prop32.Main
import Book3.Prop33.step14_ebAD
import Book3.Prop33.step14_ed0
import Book3.Prop33.step14_ed0side
import Book3.Prop33.step14_eoppd
import Book3.Prop33.step14_fgcirc
import Book3.Prop33.step14_c2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14
    (a b c₁ c c₂ d d0 e e0 f g g0 : Point) (α : Circle) (AB AD AE FG : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_d0_AD : d0.onLine AD)
    (h_dad0 : between d a d0)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_e0_AD : ¬ e0.onLine AD)
    (h_ega : between e g a) (h_afb : between a f b)
    (h_g_centre : g.isCentre α) (h_a_circ : a.onCircle α) (h_e_circ : e.onCircle α)
    (h_g_FG : g.onLine FG) (h_f_FG : f.onLine FG)
    (h_g0_FG : g0.onLine FG) (h_g0_AB : ¬ g0.onLine AB)
    (h_de0 : ∠ d:a:e0 = ∟)
    (h_dae : ∠ d:a:e = ∟) (h_bad : ∠ b:a:d < ∟)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (h_eb : e ≠ b)
    (step14_assumption1 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    (step14_assumption2 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α) :
    ∠ d:a:b = ∠ a:e:b := by
  have h_notint : ¬ AD.intersectsCircle α := step14_assumption1.2
  have h_b_circ : b.onCircle α := step14_assumption2.2.2
  have hea : e ≠ a := by euclid_finish
  have hABAD : AB ≠ AD := by euclid_finish
  have hADAE : AD ≠ AE := by euclid_finish
  have he_off : ¬ e.onLine AB := by euclid_finish
  have step14_ebAD : e.sameSide b AD := by euclid_apply (helper_3_33_step14_ebAD a b e e0 α AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "" (show AB ≠ AD; assumption)) (by euclid_assumption "" (show AD ≠ AE; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)))
  have step14_ed0 : ∠ e:a:d0 = ∟ := by euclid_apply (helper_3_33_step14_ed0 a d d0 e AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show AD ≠ AE; assumption)))
  have step14_ed0side : e.sameSide d0 AB := by euclid_apply (helper_3_33_step14_ed0side a b d d0 e e0 g α AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:d < ∟; assumption)) (by euclid_assumption "" (show e.sameSide b AD; assumption)) (by euclid_assumption "" (show ∠ e:a:d0 = ∟; assumption)))
  have step14_eoppd : e.opposingSides d AB := by euclid_apply (helper_3_33_step14_eoppd a b d d0 e AB AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show ¬ e.onLine AB; assumption)) (by euclid_assumption "" (show e.sameSide d0 AB; assumption)) (by euclid_assumption "" (show ∠ b:a:d < ∟; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))
  have step14_fgcirc : FG.intersectsCircle α := by euclid_apply (helper_3_33_step14_fgcirc g α FG (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
  have hd0_off : ¬ d0.onLine AB := by euclid_finish
  have hAB_FG : AB ≠ FG := by euclid_finish
  euclid_apply (intersections_circle_line α FG) as (c1, c2)
  by_cases hc : c1.opposingSides d0 AB
  · euclid_apply (Elements.Book3.proposition_32 a e b c1 d0 d α AD AB)
    euclid_finish
  · have step14_c2 : c2.opposingSides d0 AB := by euclid_apply (helper_3_33_step14_c2 a b c1 c2 d0 f α AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show c1.onCircle α; assumption)) (by euclid_assumption "" (show c1.onLine FG; assumption)) (by euclid_assumption "" (show c2.onCircle α; assumption)) (by euclid_assumption "" (show c2.onLine FG; assumption)) (by euclid_assumption "" (show c1 ≠ c2; assumption)) (by euclid_assumption "" (show ¬ c1.opposingSides d0 AB; assumption)) (by euclid_assumption "" (show ¬ d0.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ FG; assumption)))
    euclid_apply (Elements.Book3.proposition_32 a e b c2 d0 d α AD AB)
    euclid_finish

end Elements.Book3
