import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop24.step8_same
import Book1.Prop24.step8_diff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_24_s8
  (a b c d e f g g' g'' : Point) (AB BC AC DE EF DF DG EG FG : Line)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de_ne : d ≠ e)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
  (h_DE_ne_EF : DE ≠ EF) (h_EF_ne_DF : EF ≠ DF) (h_DF_ne_DE : DF ≠ DE)
  (h_d_DG : d.onLine DG) (h_g'_DG : g'.onLine DG) (h_between_g' : between d g' g'')
  (h_g'_sf_or_on : g'.onLine DE ∨ g'.sameSide f DE)
  (h_g'_angle : ∠ g':d:e = ∠ b:a:c)
  (h_g''_DG : g''.onLine DG) (h_between_g : between d g g'')
  (h_e_EG : e.onLine EG) (h_g_EG : g.onLine EG)
  (h_g_FG : g.onLine FG) (h_f_FG : f.onLine FG)
  (h_s3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG)
  (h_s1 : ∠ e:d:g = ∠ b:a:c) (h_bac_gt : ∠ b:a:c > ∠ e:d:f)
  (hassump1 : |(d─f)| = |(d─g)|)
  (h_s7 : ∠ d:g:f = ∠ d:f:g)
  : ∠ d:f:g > ∠ e:g:f := by
  by_cases h_same : d.sameSide g EF
  · have s8_x11 : ∠ d:f:g > ∠ e:g:f := by euclid_apply (h_1_24_s8_x2 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show |(d─f)| = |(d─g)|; assumption)) (by (show ∠ d:g:f = ∠ d:f:g; assumption)) (by (show d.sameSide g EF; assumption)))
    exact s8_x11
  · have s8_x3 : ∠ d:f:g > ∠ e:g:f := by euclid_apply (h_1_24_s8_x1 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show |(d─f)| = |(d─g)|; assumption)) (by (show ∠ d:g:f = ∠ d:f:g; assumption)) (by (show ¬d.sameSide g EF; assumption)))
    exact s8_x3

end Elements.Book1
