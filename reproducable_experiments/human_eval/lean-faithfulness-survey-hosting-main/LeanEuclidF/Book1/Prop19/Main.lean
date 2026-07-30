import SystemE
import Book1.Prop19.step1
import Book1.Prop19.step3
import Book1.Prop19.step4
import Book1.Prop19.step5
import Book1.Prop19.step7
import Book1.Prop19.step8
import Book1.Prop19.step9
import Book1.Prop19.step10
import Book1.Prop19.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_19 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) := by
  euclid_intros

  by_contra h_notgt

  have s1 : |(a─c)| = |(a─b)| ∨ |(a─c)| < |(a─b)| := by euclid_apply (h_1_19_s1 (by (show ¬|(a─c)| > |(a─b)|; assumption)))

  have hne : |(a─c)| ≠ |(a─b)| := by
    intro h_eq
    have s3 : ∠ a:b:c = ∠ b:c:a := by euclid_apply (h_1_19_s3 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a ≠ b; assumption)) (by (show |(a─c)| = |(a─b)|; assumption)))
    have s4 : False := by euclid_apply (h_1_19_s4 (by (show ∠ a:b:c > ∠ b:c:a; assumption)) (by (show ∠ a:b:c = ∠ b:c:a; assumption)))
    exact s4

  have s5 : |(a─c)| ≠ |(a─b)| := by euclid_apply (h_1_19_s5 (by (show |(a─c)| ≠ |(a─b)|; assumption)))

  have hnlt : ¬(|(a─c)| < |(a─b)|) := by
    intro h_lt
    have s7 : ∠ a:b:c < ∠ b:c:a := by euclid_apply (h_1_19_s7 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a ≠ b; assumption)) (by (show |(a─c)| < |(a─b)|; assumption)))
    have s8 : False := by euclid_apply (h_1_19_s8 (by (show ∠ a:b:c > ∠ b:c:a; assumption)) (by (show ∠ a:b:c < ∠ b:c:a; assumption)))
    exact s8

  have s9 : ¬(|(a─c)| < |(a─b)|) := by euclid_apply (h_1_19_s9 (by (show ¬(|(a─c)| < |(a─b)|); assumption)))

  have s10_a1 : |(a─c)| ≠ |(a─b)| := by assumption

  have s10 : |(a─c)| ≠ |(a─b)| := by euclid_apply (h_1_19_s10 (by (show |(a─c)| ≠ |(a─b)|; assumption)))

  have s11 : |(a─c)| > |(a─b)| := by euclid_apply (h_1_19_s11 (by (show |(a─c)| ≠ |(a─b)|; assumption)) (by (show ¬(|(a─c)| < |(a─b)|); assumption)))

  exact h_notgt s11

end Elements.Book1
