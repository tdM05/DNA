import SystemE
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step6
  (a d e f g b : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_g_AE : g.onLine AE) (h_ae : a ≠ e)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (h_g_FD : g.onLine FD) (h_fd : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_EF : ¬a.onLine EF) (h_d_EF : ¬d.onLine EF) (h_ad : ¬a.sameSide d EF)
  (h_aeb : between a e b)
  (h_ang : ∠ a:e:f = ∠ e:f:d)
  : ¬(g.opposingSides b EF) := by
  intro hop
  -- If g is on the opposite side of EF from b, then g is on the same side as a
  -- (since a and b straddle EF, e being between them).
  have hga : g.sameSide a EF := by euclid_finish
  -- g and d are on opposite sides of EF, both on FD, so f lies between g and d.
  have hbtw : between g f d := by euclid_finish
  have hgf : g ≠ f := by euclid_finish
  -- the rays e→g and e→a coincide, so ∠g:e:f = ∠a:e:f.
  have hangeq : ∠ g:e:f = ∠ a:e:f := by
    euclid_apply (equal_angles e g a f f AE EF)
    euclid_finish
  -- join f to g; triangle e-g-f has side g-f produced to d, exterior angle ∠e:f:d.
  euclid_apply (line_from_points f g) as FG
  -- Prop 1.16: ∠e:f:d > ∠g:e:f. But ∠g:e:f = ∠a:e:f = ∠e:f:d — impossible.
  euclid_apply (proposition_16 e g f d AE FG EF)
  euclid_finish

end Elements.Book1
