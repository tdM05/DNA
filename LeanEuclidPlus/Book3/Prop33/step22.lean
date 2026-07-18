import SystemE
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step22
    (a b d f : Point) (α : Circle) (AD : Line)
    (h_f_centre : f.isCentre α) (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α)
    (h_afb : between a f b) (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_da : d ≠ a)
    (step22_assumption1 : ∠ b:a:d = ∟) :
    (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  euclid_apply (proposition_16 a b f d α AD)
  euclid_finish

end Elements.Book3
