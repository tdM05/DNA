import SystemE
import Book1Variants.Prop11
import Book1.Prop13.step1
import Book1.Prop13.step2
import Book1.Prop13.step3
import Book1.Prop13.step4
import Book1.Prop13.step5
import Book1.Prop13.step6
import Book1.Prop13.step7
import Book1.Prop13.step8
import Book1.Prop13.step9
import Book1.Prop13.step10
import Book1.Prop13.step11
import Book1.Prop13.step12
import Book1.Prop13.step4_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_13 : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ := by
  euclid_intros

  by_cases h_eq : ∠ c:b:a = ∠ a:b:d
  ·

    have s1_a1 : ∠ c:b:a = ∠ a:b:d := by assumption

    have s1 : ∠ c:b:a = ∟ ∧ ∠ a:b:d = ∟ := by euclid_apply (h_1_13_s1 a b c d AB CD (by (show AB ≠ CD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between d b c; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show ∠ c:b:a = ∠ a:b:d; assumption)))
    obtain ⟨h1, h2⟩ := s1
    euclid_finish
  · euclid_apply (proposition_11' c d b a CD) as e
    euclid_apply (line_from_points b e) as BE
    have s2 : distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟ := by euclid_apply (h_1_13_s2 a b c d e AB CD BE (by (show AB ≠ CD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between d b c; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show ¬∠ c:b:a = ∠ a:b:d; assumption)) (by (show e.sameSide a CD; assumption)) (by (show ∠ c:b:e = ∟; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)))
    have s3 : ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟ := by euclid_apply (h_1_13_s3 a b c d e AB CD BE (by (show AB ≠ CD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between d b c; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.sameSide a CD; assumption)) (by (show ∠ c:b:e = ∟; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟; assumption)))
    by_cases h_cside : c.sameSide a BE
    ·

      have s4_a1 : ∠ c:b:e = ∠ c:b:a + ∠ a:b:e := by euclid_apply (h_1_13_s4_x1 a b c d e AB CD BE (by (show AB ≠ CD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between d b c; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show ¬∠ c:b:a = ∠ a:b:d; assumption)) (by (show e.sameSide a CD; assumption)) (by (show ∠ c:b:e = ∟; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show c.sameSide a BE; assumption)) (by (show distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟; assumption)) (by (show ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟; assumption)))

      have s4 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d := by euclid_apply (h_1_13_s4 (by (show ∠ c:b:e = ∠ c:b:a + ∠ a:b:e; assumption)))
      have s5 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d := by euclid_apply (h_1_13_s5 (by (show ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d; assumption)))

      have s6_a1 : ∠ d:b:a = ∠ d:b:e + ∠ e:b:a := by euclid_finish

      have s6 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c := by euclid_apply (h_1_13_s6 (by (show ∠ d:b:a = ∠ d:b:e + ∠ e:b:a; assumption)))
      have s7 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c := by euclid_apply (h_1_13_s7 (by (show ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c; assumption)))
      have s8 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c := by euclid_apply (h_1_13_s8 a b c d e BE (by (show between d b c; assumption)) (by (show a ≠ b; assumption)) (by (show distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟; assumption)) (by (show ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d; assumption)) (by (show ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c; assumption)))
      have s9 : (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
                 (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
                 (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c) := by euclid_apply (h_1_13_s9 )
      have s10 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c := by euclid_apply (h_1_13_s10 (by (show ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c; assumption)) (by (show ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c; assumption)) (by (show (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) → (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) → (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c); assumption)))
      have s11 : ∠ c:b:e + ∠ e:b:d = ∟ + ∟ := by euclid_apply (h_1_13_s11 (by (show ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟; assumption)))
      have s12 : ∠ c:b:a + ∠ a:b:d = ∟ + ∟ := by euclid_apply (h_1_13_s12 a b c d (by (show between d b c; assumption)) (by (show a ≠ b; assumption)) (by (show ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c; assumption)) (by (show ∠ c:b:e + ∠ e:b:d = ∟ + ∟; assumption)))
      exact s12
    · euclid_finish

end Elements.Book1
