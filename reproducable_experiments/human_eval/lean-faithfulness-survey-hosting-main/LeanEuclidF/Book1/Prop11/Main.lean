import SystemE
import Book1Variants.Prop01
import Book1.Prop03.Main
import Mathlib.Tactic.Linarith
import Book1.Prop11.step1
import Book1.Prop11.step2
import Book1.Prop11.step3
import Book1.Prop11.step4
import Book1.Prop11.step6
import Book1.Prop11.step7
import Book1.Prop11.step8
import Book1.Prop11.step9
import Book1.Prop11.step10
import Book1.Prop11.step11
import Book1.Prop11.hfAB
import Book1.Prop11.hperp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) := by
  euclid_intros

  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  have s1 : between a d c := by euclid_apply (h_1_11_s1 a c d (by (show between c d a; assumption)))

  euclid_apply (proposition_3 c b c d AB AB) as e
  have s2 : |(c─e)| = |(c─d)| := by euclid_apply (h_1_11_s2 c d e (by (show |(c─e)| = |(c─d)|; assumption)))

  euclid_apply (proposition_1 d e AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  have s3 : formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by euclid_apply (h_1_11_s3 a b c d e f AB DF FE (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)))

  euclid_apply (line_from_points f c) as FC
  have s4 : distinctPointsOnLine f c FC := by euclid_apply (h_1_11_s4 a b c d e f AB FC (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(c─d)| < |(c─b)|; assumption)) (by (show |(c─e)| = |(c─d)|; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)))

  have s6_a1 : |(c─d)| = |(c─e)| := by linarith

  have s6_a2 : |(c─f)| = |(c─f)| := by rfl

  have s6 : |(c─d)| = |(c─e)| ∧ |(c─f)| = |(c─f)| := by euclid_apply (h_1_11_s6 (by (show |(c─d)| = |(c─e)|; assumption)) (by (show |(c─f)| = |(c─f)|; assumption)))

  have s7 : |(d─f)| = |(f─e)| := by euclid_apply (h_1_11_s7 d e f (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))

  have s8 : ∠ d:c:f = ∠ e:c:f := by euclid_apply (h_1_11_s8 a b c d e f AB DF FE FC (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show DF ≠ AB; assumption)) (by (show AB ≠ FE; assumption)) (by (show FE ≠ DF; assumption)) (by (show |(c─d)| = |(c─e)|; assumption)) (by (show |(d─f)| = |(f─e)|; assumption)))

  have s9 : between d c e := by euclid_apply (h_1_11_s9 a b c d e AB (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show between a d c; assumption)) (by (show between c e b; assumption)))

  have s10_a1 : ∠ d:c:f = ∠ e:c:f ∧ between d c e := by euclid_finish

  have s10 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟ := by euclid_apply (h_1_11_s10 a b c d e f AB (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show ∠ d:c:f = ∠ e:c:f ∧ between d c e; assumption)))

  have s11 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟ := by euclid_apply (h_1_11_s11 (by (show ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟; assumption)))

  use f
  have hfAB : ¬(f.onLine AB) := by euclid_apply (h_1_11_x1 a b c d e f AB (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))
  have hperp : ∠ a:c:f = ∟ := by euclid_apply (h_1_11_x2 a b c d e f AB FC (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a d c; assumption)) (by (show ¬(f.onLine AB); assumption)) (by (show ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟; assumption)))
  exact ⟨hfAB, hperp⟩

end Elements.Book1
