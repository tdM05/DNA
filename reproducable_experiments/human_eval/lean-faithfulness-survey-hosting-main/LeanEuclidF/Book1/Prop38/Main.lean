import SystemE
import Book1.Prop31.Main
import Book1.Prop38.step1
import Book1.Prop38.step2
import Book1.Prop38.step3
import Book1.Prop38.step4
import Book1.Prop38.step5
import Book1.Prop38.step6
import Book1.Prop38.step7
import Book1.Prop38.step8
import Book1.Prop38.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f := by
  euclid_intros

  euclid_apply (proposition_31 b a c AC) as BG
  euclid_apply (intersection_lines AD BG) as g
  euclid_apply (proposition_31 f d e DE) as FH
  euclid_apply (intersection_lines AD FH) as h
  have s1 : g.onLine AD ∧ h.onLine AD := by euclid_apply (h_1_38_s1 g h AD (by (show g.onLine AD; assumption)) (by (show h.onLine AD; assumption)))

  have s2 : distinctPointsOnLine b g BG ∧ ¬(BG.intersectsLine AC) := by euclid_apply (h_1_38_s2 a b g AD BF BG AC AB (by (show a.onLine AD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show AB ≠ BF; assumption)) (by (show b.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show g.onLine AD; assumption)) (by (show b.onLine BF; assumption)) (by (show ¬AD.intersectsLine BF; assumption)) (by (show ¬BG.intersectsLine AC; assumption)))

  have s3 : distinctPointsOnLine f h FH ∧ ¬(FH.intersectsLine DE) := by euclid_apply (h_1_38_s3 d e f h AD BF FH DE (by (show d.onLine AD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine BF; assumption)) (by (show DE ≠ BF; assumption)) (by (show f.onLine FH; assumption)) (by (show h.onLine FH; assumption)) (by (show h.onLine AD; assumption)) (by (show f.onLine BF; assumption)) (by (show ¬AD.intersectsLine BF; assumption)) (by (show ¬FH.intersectsLine DE; assumption)))

  have s4 : formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF := by euclid_apply (h_1_38_s4 a b c d e f g h AD BF AB AC DE BG FH (by (show a.onLine AD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BF; assumption)) (by (show c.onLine BF; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BF; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show DE ≠ BF; assumption)) (by (show b.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show g.onLine AD; assumption)) (by (show ¬BG.intersectsLine AC; assumption)) (by (show f.onLine FH; assumption)) (by (show h.onLine FH; assumption)) (by (show h.onLine AD; assumption)) (by (show ¬FH.intersectsLine DE; assumption)) (by (show between b c f; assumption)) (by (show between b e f; assumption)) (by (show ¬AD.intersectsLine BF; assumption)))

  have s5_a1 : |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF) := by euclid_finish

  have s5 : Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h := by euclid_apply (h_1_38_s5 a b c d e f g h AD BF AB AC DE BG FH (by (show a.onLine AD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BF; assumption)) (by (show c.onLine BF; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BF; assumption)) (by (show BF ≠ AC; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show e.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show DE ≠ BF; assumption)) (by (show b.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show g.onLine AD; assumption)) (by (show ¬BG.intersectsLine AC; assumption)) (by (show f.onLine FH; assumption)) (by (show h.onLine FH; assumption)) (by (show h.onLine AD; assumption)) (by (show ¬FH.intersectsLine DE; assumption)) (by (show between b c f; assumption)) (by (show between b e f; assumption)) (by (show ¬AD.intersectsLine BF; assumption)) (by (show formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF; assumption)) (by (show |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF); assumption)))

  have s6_a1 : formParallelogram g b a c BG AC AD BF := by euclid_finish

  have s6 : Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a := by euclid_apply (h_1_38_s6 a b c g AD BF AB AC BG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show formParallelogram g b a c BG AC AD BF; assumption)))

  have s7_a1 : formParallelogram d e h f DE FH AD BF := by euclid_finish

  have s7 : Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h := by euclid_apply (h_1_38_s7 d e f h AD BF DE FH DF (by (show d.onLine AD; assumption)) (by (show h.onLine AD; assumption)) (by (show h.onLine FH; assumption)) (by (show f.onLine FH; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show ¬FH.intersectsLine DE; assumption)) (by (show ¬AD.intersectsLine BF; assumption)) (by (show DE ≠ BF; assumption)) (by (show formParallelogram d e h f DE FH AD BF; assumption)))

  have s8 : (Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧ Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧ Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) → Triangle.area △ a:b:c = Triangle.area △ f:e:d := by euclid_apply (h_1_38_s8 a b c d e f g h)

  have s9 : Triangle.area △ a:b:c = Triangle.area △ d:e:f := by euclid_apply (h_1_38_s9 a b c d e f g h (by (show Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h; assumption)) (by (show Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a; assumption)) (by (show Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h; assumption)) (by (show (Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧ Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧ Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) → Triangle.area △ a:b:c = Triangle.area △ f:e:d; assumption)))

  exact s9

end Elements.Book1
