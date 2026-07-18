import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step23_assumption1
    (a b e f : Point) (α : Circle) (AB : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_f_centre : f.isCentre α)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α) (h_e_circ : e.onCircle α)
    (h_e_off : ¬ e.onLine AB) (h_ab : a ≠ b) :
    ∠ a:e:b = ∟ := by
  have hfae : |(f─a)| = |(f─e)| := by euclid_finish
  have hfbe : |(f─b)| = |(f─e)| := by euclid_finish
  euclid_apply (line_from_points a e) as AEl
  euclid_apply (line_from_points e b) as EBl
  euclid_apply (extend_point EBl e b) as dd
  euclid_apply (Elements.Book1.proposition_32 a e b dd AEl EBl AB)
  euclid_finish

end Elements.Book3
