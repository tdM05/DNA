import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop23
import Mathlib.Tactic.Linarith
import Book1.Prop24.step1
import Book1.Prop24.step2
import Book1.Prop24.step3
import Book1.Prop24.step4
import Book1.Prop24.step5
import Book1.Prop24.step6
import Book1.Prop24.step7
import Book1.Prop24.step8
import Book1.Prop24.step9
import Book1.Prop24.step10
import Book1.Prop24.step11
import Book1.Prop24.step12
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| := by
  euclid_intros

  euclid_apply (proposition_23' d e a b c f DE AB AC) as g'
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g

  have s1_a1 : ∠ b:a:c > ∠ e:d:f := by assumption

  have s1 : ∠ e:d:g = ∠ b:a:c := by euclid_apply (h_1_24_s1 d e g g' g'' DE DG (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show between d g g''; assumption)) (by (show g' ≠ d; assumption)) (by (show d ≠ e; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)))

  have s2 : |(d─g)| = |(a─c)| ∨ |(d─g)| = |(d─f)| := by euclid_apply (h_1_24_s2 d g a c (by (show |(d─g)| = |(a─c)|; assumption)))

  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  have s3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG := by euclid_apply (h_1_24_s3 d e g f DE EF DF DG EG FG (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)))

  have s4_a1 : |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)| := by euclid_finish

  have s4 : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)| := by euclid_apply (h_1_24_s4 (by (show |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|; assumption)))

  have s5 : ∠ b:a:c = ∠ e:d:g := by euclid_apply (h_1_24_s5 (by (show ∠ e:d:g = ∠ b:a:c; assumption)))

  have s6 : |(b─c)| = |(e─g)| := by euclid_apply (h_1_24_s6 a b c d e g g'' AB BC AC DE EG DG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show d.onLine DG; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|; assumption)) (by (show ∠ b:a:c = ∠ e:d:g; assumption)))

  have s7_a1 : |(d─f)| = |(d─g)| := by linarith

  have s7 : ∠ d:g:f = ∠ d:f:g := by euclid_apply (h_1_24_s7 a b c d e g f g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show |(d─f)| = |(d─g)|; assumption)))

  have s8 : ∠ d:f:g > ∠ e:g:f := by euclid_apply (h_1_24_s8 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show |(d─f)| = |(d─g)|; assumption)) (by (show ∠ d:g:f = ∠ d:f:g; assumption)))

  have s9 : ∠ e:f:g > ∠ e:g:f := by euclid_apply (h_1_24_s9 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show |(d─f)| = |(d─g)|; assumption)) (by (show ∠ d:g:f = ∠ d:f:g; assumption)) (by (show ∠ d:f:g > ∠ e:g:f; assumption)))

  have s10_a1 : ∠ e:f:g > ∠ e:g:f := by assumption

  have s10 : |(e─g)| > |(e─f)| := by euclid_apply (h_1_24_s10 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d.onLine DG; assumption)) (by (show g'.onLine DG; assumption)) (by (show between d g' g''; assumption)) (by (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by (show ∠ g':d:e = ∠ b:a:c; assumption)) (by (show g''.onLine DG; assumption)) (by (show between d g g''; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.onLine FG; assumption)) (by (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by (show ∠ e:d:g = ∠ b:a:c; assumption)) (by (show ∠ b:a:c > ∠ e:d:f; assumption)) (by (show ∠ e:f:g > ∠ e:g:f; assumption)))

  have s11 : |(e─g)| = |(b─c)| := by euclid_apply (h_1_24_s11 b c e g (by (show |(b─c)| = |(e─g)|; assumption)))

  have s12 : |(b─c)| > |(e─f)| := by euclid_apply (h_1_24_s12 b c e f g (by (show |(e─g)| > |(e─f)|; assumption)) (by (show |(e─g)| = |(b─c)|; assumption)))

  exact s12

end Elements.Book1
