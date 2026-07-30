import SystemE
import Book1.Prop25.step1
import Book1.Prop25.step3
import Book1.Prop25.step4
import Book1.Prop25.step5
import Book1.Prop25.step7
import Book1.Prop25.step8
import Book1.Prop25.step9
import Book1.Prop25.step10
import Book1.Prop25.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_25 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (|(b─c)| > |(e─f)|) →
  (∠ b:a:c > ∠ e:d:f) := by
  euclid_intros

  by_contra h_notgt

  have s1 : ∠ b:a:c = ∠ e:d:f ∨ ∠ b:a:c < ∠ e:d:f := by euclid_apply (h_1_25_s1 (by (show ¬∠ b:a:c > ∠ e:d:f; assumption)))

  have hne : ∠ b:a:c ≠ ∠ e:d:f := by
    intro h_eq
    have s3 : |(b─c)| = |(e─f)| := by euclid_apply (h_1_25_s3 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show ∠ b:a:c = ∠ e:d:f; assumption)))
    have s4 : False := by euclid_apply (h_1_25_s4 (by (show |(b─c)| > |(e─f)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))
    exact s4

  have s5 : ∠ b:a:c ≠ ∠ e:d:f := by euclid_apply (h_1_25_s5 (by (show ∠ b:a:c ≠ ∠ e:d:f; assumption)))

  have hnlt : ¬(∠ b:a:c < ∠ e:d:f) := by
    intro h_lt
    have s7 : |(b─c)| < |(e─f)| := by euclid_apply (h_1_25_s7 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show ∠ b:a:c < ∠ e:d:f; assumption)))
    have s8 : False := by euclid_apply (h_1_25_s8 (by (show |(b─c)| > |(e─f)|; assumption)) (by (show |(b─c)| < |(e─f)|; assumption)))
    exact s8

  have s9 : ¬(∠ b:a:c < ∠ e:d:f) := by euclid_apply (h_1_25_s9 (by (show ¬(∠ b:a:c < ∠ e:d:f); assumption)))

  have s10 : ∠ b:a:c ≠ ∠ e:d:f := by euclid_apply (h_1_25_s10 (by (show ∠ b:a:c ≠ ∠ e:d:f; assumption)))

  have s11 : ∠ b:a:c > ∠ e:d:f := by euclid_apply (h_1_25_s11 (by (show ∠ b:a:c ≠ ∠ e:d:f; assumption)) (by (show ¬(∠ b:a:c < ∠ e:d:f); assumption)))

  exact h_notgt s11

end Elements.Book1
