import SystemE
import Book1.Prop41.step1
import Book1.Prop41.step2
import Book1.Prop41.step3
import Book1.Prop41.step4
import Book1.Prop41.step3_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) := by
  euclid_intros

  euclid_apply (line_from_points a c) as AC
  have s1 : distinctPointsOnLine a c AC := by euclid_apply (h_1_41_s1 a b c CD AC (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine CD; assumption)) (by (show a.sameSide b CD; assumption)))

  have s2_a1 : distinctPointsOnLine b c BC := by euclid_finish

  have s2_a2 : ¬(AE.intersectsLine BC) := by assumption

  have s2 : Triangle.area △ a:b:c = Triangle.area △ e:b:c := by euclid_apply (h_1_41_s2 a b c e AE BC AB CD AC BE CE (by (show a.onLine AE; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show a.sameSide b CD; assumption)) (by (show e.onLine AE; assumption)) (by (show e.onLine BE; assumption)) (by (show b.onLine BE; assumption)) (by (show e ≠ b; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show BE ≠ BC; assumption)) (by (show BC ≠ CE; assumption)) (by (show CE ≠ BE; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show distinctPointsOnLine a c AC; assumption)) (by (show distinctPointsOnLine b c BC; assumption)) (by (show ¬(AE.intersectsLine BC); assumption)))

  have s3_a1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by euclid_apply (h_1_41_s3_x1 a b c d AE BC AB CD AC (by (show a.onLine AE; assumption)) (by (show d.onLine AE; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AE.intersectsLine BC; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show distinctPointsOnLine a c AC; assumption)))

  have s3 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c := by euclid_apply (h_1_41_s3 a b c d AE BC AB CD AC (by (show a.onLine AE; assumption)) (by (show d.onLine AE; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AE.intersectsLine BC; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show distinctPointsOnLine a c AC; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ a:c:d; assumption)))

  have s4 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ e:b:c + Triangle.area △ e:b:c := by euclid_apply (h_1_41_s4 (by (show Triangle.area △ a:b:c = Triangle.area △ e:b:c; assumption)) (by (show Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c; assumption)))

  exact s4

end Elements.Book1
