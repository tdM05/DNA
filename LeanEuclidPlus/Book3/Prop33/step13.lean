import SystemE
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step13
    (a d e g : Point) (α : Circle) (AD : Line)
    (h_g_centre : g.isCentre α) (h_a_circ : a.onCircle α) (h_e_circ : e.onCircle α)
    (h_ega : between e g a) (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_da : d ≠ a)
    (step13_assumption1 : ∠ d:a:e = ∟) :
    (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  euclid_apply (proposition_16 a e g d α AD)
  euclid_finish

end Elements.Book3
