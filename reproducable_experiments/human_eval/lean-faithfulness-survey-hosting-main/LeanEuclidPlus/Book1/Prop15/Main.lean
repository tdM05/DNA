import SystemE
import Book1.Prop15.step1
import Book1.Prop15.step2
import Book1.Prop15.step3
import Book1.Prop15.step4
import Book1.Prop15.step5
import Book1.Prop15.step6
import Book1.Prop15.step7
import Book1.Prop15.h1
import Book1.Prop15.h2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_15 : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) := by
  euclid_intros

  have s1_a1 : between d e c := by assumption

  have s1 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟ := by euclid_apply (h_1_15_s1 a b c d e AB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine CD; assumption)) (by (show CD ≠ AB; assumption)) (by (show between a e b; assumption)) (by (show between d e c; assumption)))

  have s2_a1 : between a e b := by assumption

  have s2 : ∠ a:e:d + ∠ d:e:b = ∟ + ∟ := by euclid_apply (h_1_15_s2 a b d e AB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine CD; assumption)) (by (show e.onLine CD; assumption)) (by (show e.onLine AB; assumption)) (by (show CD ≠ AB; assumption)) (by (show between d e c; assumption)) (by (show between a e b; assumption)))

  have s3 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟ := by euclid_apply (h_1_15_s3 c e a d (by (show ∠ c:e:a + ∠ a:e:d = ∟ + ∟; assumption)))

  have s4 : ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b := by euclid_apply (h_1_15_s4 c e a d b (by (show ∠ c:e:a + ∠ a:e:d = ∟ + ∟; assumption)) (by (show ∠ a:e:d + ∠ d:e:b = ∟ + ∟; assumption)))

  have s5 : ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d := by euclid_apply (h_1_15_s5 c e a d b (by (show ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b; assumption)))

  have s6 : ∠ c:e:a = ∠ b:e:d := by euclid_apply (h_1_15_s6 c e a d b (by (show between d e c; assumption)) (by (show between a e b; assumption)) (by (show ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d; assumption)))

  have s7 : ∠ c:e:b = ∠ d:e:a := by euclid_apply (h_1_15_s7 a b c d e AB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine AB; assumption)) (by (show e.onLine CD; assumption)) (by (show CD ≠ AB; assumption)) (by (show between d e c; assumption)) (by (show between a e b; assumption)) (by (show ∠ a:e:d + ∠ d:e:b = ∟ + ∟; assumption)))

  have h1 : ∠ a:e:c = ∠ d:e:b := by euclid_apply (h_1_15_x1 a e c d b (by (show between d e c; assumption)) (by (show between a e b; assumption)) (by (show ∠ c:e:a = ∠ b:e:d; assumption)))
  have h2 : ∠ c:e:b = ∠ a:e:d := by euclid_apply (h_1_15_x2 c e b d a (by (show between d e c; assumption)) (by (show between a e b; assumption)) (by (show ∠ c:e:b = ∠ d:e:a; assumption)))
  exact ⟨h1, h2⟩

end Elements.Book1
