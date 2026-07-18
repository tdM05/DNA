import SystemE
import Book3.Prop16.Main
import Book3.Prop33.h_dee
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step38
    (a d d0 e0 g : Point) (α : Circle) (AD AE : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_d0_AD : d0.onLine AD)
    (h_dad0 : between d a d0)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE) (h_g_AE : g.onLine AE)
    (h_g_centre : g.isCentre α) (h_a_circ : a.onCircle α) (h_da : d ≠ a)
    (step38_assumption1 : ∠ d:a:e0 = ∟) :
    (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  have hga : g ≠ a := by euclid_finish
  euclid_apply (intersection_circle_line_extending_points α AE g a) as ee
  have h_dee : ∠ d:a:ee = ∟ := by euclid_apply (helper_3_33_h_dee a d e0 ee g AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show ee.onLine AE; assumption)) (by euclid_assumption "" (show between ee g a; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)))
  euclid_apply (proposition_16 a ee g d α AD)
  euclid_finish

end Elements.Book3
