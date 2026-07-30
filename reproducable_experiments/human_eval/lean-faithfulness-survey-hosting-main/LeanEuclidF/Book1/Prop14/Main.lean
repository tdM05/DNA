import SystemE
import Book1.Prop14.step1
import Book1.Prop14.step2
import Book1.Prop14.step3
import Book1.Prop14.step4
import Book1.Prop14.step5
import Book1.Prop14.step6
import Book1.Prop14.step7
import Book1.Prop14.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_14 : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD := by
  euclid_intros

  have habsurd : ¬ (BC ≠ BD) := by
    intro hne
    euclid_apply (extend_point BC c b) as e

    have s1_a1 : BD ≠ BC := by euclid_finish

    have s1 : between c b e := by euclid_apply (h_1_14_s1 c b e BC BD (by (show between c b e; assumption)) (by (show BD ≠ BC; assumption)))

    have s2_a1 : between c b e := by assumption

    have s2 : ∠ a:b:c + ∠ a:b:e = ∟ + ∟ := by euclid_apply (h_1_14_s2 a b c e AB BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show e.onLine BC; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show between c b e; assumption)))

    have s3 : ∠ a:b:c + ∠ a:b:d = ∟ + ∟ := by euclid_apply (h_1_14_s3 a b c d (by (show ∠ a:b:c + ∠ a:b:d = ∟ + ∟; assumption)))

    have s4 : ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d := by euclid_apply (h_1_14_s4 a b c d e (by (show ∠ a:b:c + ∠ a:b:e = ∟ + ∟; assumption)) (by (show ∠ a:b:c + ∠ a:b:d = ∟ + ∟; assumption)))

    have s5 : ∠ a:b:e = ∠ a:b:d := by euclid_apply (h_1_14_s5 a b c d e (by (show ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d; assumption)))

    have s6 : ∠ a:b:e = ∠ a:b:d := by euclid_apply (h_1_14_s6 a b d e (by (show ∠ a:b:e = ∠ a:b:d; assumption)))

    have s7 : False := by euclid_apply (h_1_14_s7 a b c d e AB BC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show ¬d.onLine AB; assumption)) (by (show ¬c.sameSide d AB; assumption)) (by (show BC ≠ BD; assumption)) (by (show e.onLine BC; assumption)) (by (show between c b e; assumption)) (by (show ∠ a:b:c + ∠ a:b:e = ∟ + ∟; assumption)) (by (show ∠ a:b:e = ∠ a:b:d; assumption)))

    exact s7

  have s10 : BC = BD := by euclid_apply (h_1_14_s10 BC BD (by (show ¬ BC ≠ BD; assumption)))

  exact s10

end Elements.Book1
