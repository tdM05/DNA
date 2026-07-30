import SystemE
import Book1.Prop03.Main
import Book1.Prop10.Main
import Mathlib.Tactic.Linarith
import Book1.Prop16.step1
import Book1.Prop16.step2
import Book1.Prop16.step3
import Book1.Prop16.step4
import Book1.Prop16.step5
import Book1.Prop16.step6
import Book1.Prop16.step7
import Book1.Prop16.step8
import Book1.Prop16.step9
import Book1.Prop16.step10
import Book1.Prop16.step11
import Book1.Prop16.step12
import Book1.Prop16.step13
import Book1.Prop16.step14
import Book1.Prop16.h1
import Book1.Prop16.h2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_16 : ∀ (a b c d : Point) (AB BC AC: Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c) := by
  euclid_intros

  euclid_apply (proposition_10 a c AC) as e
  have s1 : between a e c ∧ |(a─e)| = |(e─c)| := by euclid_apply (h_1_16_s1 a e c (by (show between a e c; assumption)) (by (show |(a─e)| = |(e─c)|; assumption)))

  euclid_apply (line_from_points b e) as BE
  euclid_apply (extend_point_longer BE b e (b─e)) as f'
  euclid_apply (proposition_3 e f' b e BE BE) as f

  have s2_a1 : distinctPointsOnLine b e BE := by euclid_finish

  have s2 : between b e f := by euclid_apply (h_1_16_s2 b e f f' BE (by (show between b e f'; assumption)) (by (show between e f f'; assumption)) (by (show distinctPointsOnLine b e BE; assumption)))

  have s3 : |(e─f)| = |(b─e)| := by euclid_apply (h_1_16_s3 b e f (by (show |(e─f)| = |(b─e)|; assumption)))

  euclid_apply (line_from_points f c) as FC
  have s4 : distinctPointsOnLine f c FC := by euclid_apply (h_1_16_s4 a b c e f AC BC AB BE FC (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show between b e f; assumption)) (by (show between a e c; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show BC ≠ AC; assumption)))

  euclid_apply (extend_point AC a c) as g
  have s5 : between a c g := by euclid_apply (h_1_16_s5 a c g (by (show between a c g; assumption)))

  have s6_a1 : |(a─e)| = |(e─c)| := by assumption

  have s6_a2 : |(b─e)| = |(e─f)| := by linarith

  have s6 : |(a─e)| = |(c─e)| ∧ |(b─e)| = |(e─f)| := by euclid_apply (h_1_16_s6 a b c e f (by (show |(a─e)| = |(e─c)|; assumption)) (by (show |(b─e)| = |(e─f)|; assumption)))

  have s7 : ∠ a:e:b = ∠ f:e:c := by euclid_apply (h_1_16_s7 a b c e f AB BC AC BE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show between a e c; assumption)) (by (show between b e f; assumption)))

  have s8 : |(a─b)| = |(f─c)| := by euclid_apply (h_1_16_s8 a b c e f AB BC AC BE FC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a e c; assumption)) (by (show between b e f; assumption)) (by (show |(a─e)| = |(e─c)|; assumption)) (by (show |(b─e)| = |(e─f)|; assumption)) (by (show ∠ a:e:b = ∠ f:e:c; assumption)))

  have s9 : Triangle.area △ a:b:e = Triangle.area △ f:e:c := by euclid_apply (h_1_16_s9 a b c e f AB BC AC BE FC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a e c; assumption)) (by (show between b e f; assumption)) (by (show |(a─e)| = |(e─c)|; assumption)) (by (show |(b─e)| = |(e─f)|; assumption)) (by (show ∠ a:e:b = ∠ f:e:c; assumption)))

  have s10 : (∠ b:a:e = ∠ e:c:f) ∧ (∠ a:b:e = ∠ c:f:e) := by euclid_apply (h_1_16_s10 a b c e f AB BC AC BE FC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a e c; assumption)) (by (show between b e f; assumption)) (by (show |(a─e)| = |(e─c)|; assumption)) (by (show |(b─e)| = |(e─f)|; assumption)) (by (show ∠ a:e:b = ∠ f:e:c; assumption)))

  have s11 : ∠ b:a:e = ∠ e:c:f := by euclid_apply (h_1_16_s11 a b c e f (by (show (∠ b:a:e = ∠ e:c:f) ∧ (∠ a:b:e = ∠ c:f:e); assumption)))

  have s12 : ∠ e:c:d > ∠ e:c:f := by euclid_apply (h_1_16_s12 a b c d e f AB BC AC BE FC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between b c d; assumption)) (by (show between a e c; assumption)) (by (show between b e f; assumption)) (by (show ∠ a:e:b = ∠ f:e:c; assumption)) (by (show ∠ b:a:e = ∠ e:c:f; assumption)))

  have s13 : ∠ a:c:d > ∠ b:a:e := by euclid_apply (h_1_16_s13 a b c d e f AC BC (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show between a e c; assumption)) (by (show between b c d; assumption)) (by (show ∠ b:a:e = ∠ e:c:f; assumption)) (by (show ∠ e:c:d > ∠ e:c:f; assumption)))

  have s14 : ∠ a:c:d > ∠ a:b:c := by euclid_apply (h_1_16_s14 a b c d g AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b c d; assumption)) (by (show between a c g; assumption)) (by (show g.onLine AC; assumption)))

  have h1 : ∠ a:c:d > ∠ c:b:a := by euclid_apply (h_1_16_x1 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:d > ∠ a:b:c; assumption)))
  have h2 : ∠ a:c:d > ∠ b:a:c := by euclid_apply (h_1_16_x2 a b c d e AB AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a e c; assumption)) (by (show ∠ a:c:d > ∠ b:a:e; assumption)))
  exact ⟨h1, h2⟩

end Elements.Book1
