import SystemE
import Book1.Prop31.Main
import Book1.Prop39.step1
import Book1.Prop39.step3
import Book1.Prop39.step4
import Book1.Prop39.step5
import Book1.Prop39.step6
import Book1.Prop39.step7
import Book1.Prop39.step8
import Book1.Prop39.step9
import Book1.Prop39.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) := by
  euclid_intros

  have s1 : distinctPointsOnLine a d AD := by euclid_apply (h_1_39_s1 a d AD (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)))

  euclid_apply (proposition_31 a b c BC) as AE
  have s3 : a.onLine AE ∧ ¬(AE.intersectsLine BC) := by euclid_apply (h_1_39_s3 a AE BC (by (show a.onLine AE; assumption)) (by (show ¬AE.intersectsLine BC; assumption)))

  euclid_apply (intersection_lines AE BD) as e
  euclid_apply (line_from_points e c) as EC
  have s4 : distinctPointsOnLine e c EC := by euclid_apply (h_1_39_s4 a d e c AE BC EC (by (show a.onLine AE; assumption)) (by (show a.sameSide d BC; assumption)) (by (show e.onLine AE; assumption)) (by (show c.onLine BC; assumption)) (by (show ¬AE.intersectsLine BC; assumption)) (by (show e.onLine EC; assumption)) (by (show c.onLine EC; assumption)))

  have s5_a1 : ¬(AE.intersectsLine BC) := by assumption

  have s5 : Triangle.area △ a:b:c = Triangle.area △ e:b:c := by euclid_apply (h_1_39_s5 a b c d e AB BC AC BD CD EC AE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show e.onLine BD; assumption)) (by (show c.onLine EC; assumption)) (by (show e.onLine EC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show ¬(AE.intersectsLine BC); assumption)))

  have s6 : Triangle.area △ a:b:c = Triangle.area △ d:b:c := by euclid_apply (h_1_39_s6 a b c d (by (show Triangle.area △ a:b:c = Triangle.area △ d:b:c; assumption)))

  have s7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c := by euclid_apply (h_1_39_s7 a b c d e (by (show Triangle.area △ a:b:c = Triangle.area △ e:b:c; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ d:b:c; assumption)))

  have s8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c := by euclid_apply (h_1_39_s8 a b c d e AB BC AC BD CD AD AE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show e.onLine BD; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show ¬AE.intersectsLine BC; assumption)) (by (show AD.intersectsLine BC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ d:b:c; assumption)))

  have s9 : AE.intersectsLine BC := by euclid_apply (h_1_39_s9 d e b c AE BC (by (show Triangle.area △ d:b:c = Triangle.area △ e:b:c; assumption)) (by (show Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c; assumption)))

  have s11 : ¬(AD.intersectsLine BC) := by euclid_apply (h_1_39_s11 d e b c AD BC (by (show Triangle.area △ d:b:c = Triangle.area △ e:b:c; assumption)) (by (show Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c; assumption)))

  exact s11 ‹AD.intersectsLine BC›

end Elements.Book1
