import SystemE
import Book1.Prop31.Main
import Book1.Prop32.step1
import Book1.Prop32.step2
import Book1.Prop32.step3
import Book1.Prop32.step4
import Book1.Prop32.step5
import Book1.Prop32.step6
import Book1.Prop32.step7
import Book1.Prop32.step8
import Book1.Prop32.step9
import Book1.Prop32.hgoal1
import Book1.Prop32.hgoal2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_32 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by
  euclid_intros

  euclid_apply (proposition_31 c a b AB) as CE
  euclid_apply (point_on_line_same_side BC CE a) as e
  have s1 : c.onLine CE ∧ e.onLine CE ∧ ¬(CE.intersectsLine AB) := by euclid_apply (h_1_32_s1 c e AB CE (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬CE.intersectsLine AB; assumption)))

  have s2_a1 : ¬(AB.intersectsLine CE) := by euclid_finish

  have s2_a2 : distinctPointsOnLine a c AC := by euclid_finish

  have s2 : ∠ b:a:c = ∠ a:c:e := by euclid_apply (h_1_32_s2 a b c e AB BC AC CE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬CE.intersectsLine AB; assumption)) (by (show e.sameSide a BC; assumption)) (by (show ¬(AB.intersectsLine CE); assumption)) (by (show distinctPointsOnLine a c AC; assumption)))

  have s3_a1 : ¬(AB.intersectsLine CE) := by assumption

  have s3_a2 : distinctPointsOnLine b d BC := by euclid_finish

  have s3 : ∠ e:c:d = ∠ a:b:c := by euclid_apply (h_1_32_s3 a b c d e AB BC AC CE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show between b c d; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬CE.intersectsLine AB; assumption)) (by (show e.sameSide a BC; assumption)) (by (show ¬(AB.intersectsLine CE); assumption)) (by (show distinctPointsOnLine b d BC; assumption)))

  have s4 : ∠ a:c:e = ∠ b:a:c := by euclid_apply (h_1_32_s4 a b c e AB BC AC CE (by (show ∠ b:a:c = ∠ a:c:e; assumption)))

  have s5 : ∠ a:c:d = ∠ b:a:c + ∠ a:b:c := by euclid_apply (h_1_32_s5 a b c d e AB BC AC CE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b c d; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬CE.intersectsLine AB; assumption)) (by (show e.sameSide a BC; assumption)) (by (show ¬AB.intersectsLine CE; assumption)) (by (show distinctPointsOnLine a c AC; assumption)) (by (show distinctPointsOnLine b d BC; assumption)))

  have s6 : ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b := by euclid_apply (h_1_32_s6 a b c d AB BC AC (by (show ∠ a:c:d = ∠ b:a:c + ∠ a:b:c; assumption)))

  have s7 : ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b := by euclid_apply (h_1_32_s7 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b; assumption)))

  have s8 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟ := by euclid_apply (h_1_32_s8 a b c d AB BC AC (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show BC ≠ AC; assumption)) (by (show between b c d; assumption)) (by (show distinctPointsOnLine a c AC; assumption)) (by (show distinctPointsOnLine b d BC; assumption)))

  have s9 : ∠ a:c:b + ∠ c:b:a + ∠ c:a:b = ∟ + ∟ := by euclid_apply (h_1_32_s9 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b; assumption)) (by (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  have hgoal1 : ∠ a:c:d = ∠ c:a:b + ∠ a:b:c := by euclid_apply (h_1_32_x1 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:d = ∠ b:a:c + ∠ a:b:c; assumption)))
  have hgoal2 : ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by euclid_apply (h_1_32_x2 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:b + ∠ c:b:a + ∠ c:a:b = ∟ + ∟; assumption)))
  exact ⟨hgoal1, hgoal2⟩

end Elements.Book1
