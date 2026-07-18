import SystemE
import Book3.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step39
    (a b d d0 h h' : Point) (α : Circle) (AD AB : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_d0_AD : d0.onLine AD)
    (h_dad0 : between d a d0)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α)
    (h_h_circ : h.onCircle α) (h_h'_circ : h'.onCircle α)
    (h_h_opp : h.opposingSides d AB) (h_h'_opp : h'.opposingSides d0 AB)
    (h_step38 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    (step39_assumption1 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α) :
    ∠ b:a:d = ∠ a:h:b := by
  have h_notint : ¬ AD.intersectsCircle α := h_step38.2
  euclid_apply (Elements.Book3.proposition_32 a h b h' d0 d α AD AB)
  euclid_finish

end Elements.Book3
