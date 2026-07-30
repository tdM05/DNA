import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop05
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
import Book1.Prop18.step1
import Book1.Prop18.step2
import Book1.Prop18.step3
import Book1.Prop18.step4
import Book1.Prop18.step5
import Book1.Prop18.step6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_18 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) := by
  euclid_intros

  euclid_apply (proposition_3 a c a b AC AB) as d
  have s1 : |(a─d)| = |(a─b)| := by euclid_apply (h_1_18_s1 a b d (by (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (line_from_points b d) as BD
  have s2 : distinctPointsOnLine b d BD := by euclid_apply (h_1_18_s2 a b c d AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a d c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)))

  have s3_a1 : between a d c := by assumption

  have s3 : ∠ a:d:b > ∠ d:c:b := by euclid_apply (h_1_18_s3 a b c d AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show between a d c; assumption)))

  have s4_a1 : |(a─b)| = |(a─d)| := by linarith

  have s4 : ∠ a:d:b = ∠ a:b:d := by euclid_apply (h_1_18_s4 a b d AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show between a d c; assumption)) (by (show |(a─b)| = |(a─d)|; assumption)))

  have s5 : ∠ a:b:d > ∠ b:c:a := by euclid_apply (h_1_18_s5 a b c d BC AC (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show BC ≠ AC; assumption)) (by (show between a d c; assumption)) (by (show ∠ a:d:b > ∠ d:c:b; assumption)) (by (show ∠ a:d:b = ∠ a:b:d; assumption)))

  have s6 : ∠ a:b:c > ∠ b:c:a := by euclid_apply (h_1_18_s6 a b c d AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show between a d c; assumption)) (by (show ∠ a:b:d > ∠ b:c:a; assumption)))

  exact s6

end Elements.Book1
