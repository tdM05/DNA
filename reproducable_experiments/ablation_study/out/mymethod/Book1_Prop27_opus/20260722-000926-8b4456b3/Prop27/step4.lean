import SystemE
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step4
  (a d e f g b : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_g_AE : g.onLine AE)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_g_FD : g.onLine FD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_EF : ¬a.onLine EF) (h_d_EF : ¬d.onLine EF)
  (h_aeb : between a e b)
  (h_gb : g.sameSide b EF)
  (h_ang3 : ∠ a:e:f = ∠ e:f:g)
  : False := by
  -- e lies between a and g: a,b are opposite across EF (e on EF), g on b's side, all on AE.
  have hbtw : between g e a := by euclid_finish
  -- join f to g, then triangle f-g-e has exterior angle at e (side g-e produced to a).
  euclid_apply (line_from_points f g) as FG
  -- Prop 1.16: the external angle ∠f:e:a exceeds the interior opposite angle ∠g:f:e.
  euclid_apply (proposition_16 f g e a FG AE EF)
  -- ∠f:e:a = ∠a:e:f and ∠g:f:e = ∠e:f:g, but step3 makes them equal — impossible.
  euclid_finish

end Elements.Book1
