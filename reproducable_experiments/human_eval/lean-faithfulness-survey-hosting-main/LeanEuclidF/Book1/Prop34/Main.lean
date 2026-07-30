import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop34.step1
import Book1.Prop34.step2
import Book1.Prop34.step3
import Book1.Prop34.step4
import Book1.Prop34.step5
import Book1.Prop34.step6
import Book1.Prop34.step7
import Book1.Prop34.step8
import Book1.Prop34.step9
import Book1.Prop34.step10
import Book1.Prop34.step12
import Book1.Prop34.step13
import Book1.Prop34.step14
import Book1.Prop34.step15
import Book1.Prop34.step16
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b := by
  euclid_intros

  have s1_a1 : ¬(AB.intersectsLine CD) := by assumption

  have s1_a2 : b.onLine AB ∧ b.onLine BC ∧ c.onLine CD ∧ c.onLine BC := by euclid_finish

  have s1 : ∠ a:b:c = ∠ b:c:d := by euclid_apply (h_1_34_s1 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show b.onLine AB ∧ b.onLine BC ∧ c.onLine CD ∧ c.onLine BC; assumption)))

  have s2_a1 : ¬(AC.intersectsLine BD) := by assumption

  have s2_a2 : c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC := by euclid_finish

  have s2 : ∠ a:c:b = ∠ c:b:d := by euclid_apply (h_1_34_s2 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC; assumption)))

  have s3_a1 : ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d := by euclid_finish

  have s3 : formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD := by euclid_apply (h_1_34_s3 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d; assumption)))

  have s4 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b := by euclid_apply (h_1_34_s4 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)) (by (show ∠ a:c:b = ∠ c:b:d; assumption)) (by (show formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD; assumption)))

  have s5 : |(a─b)| = |(c─d)| := by euclid_apply (h_1_34_s5 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  have s6 : |(a─c)| = |(b─d)| := by euclid_apply (h_1_34_s6 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  have s7 : ∠ b:a:c = ∠ c:d:b := by euclid_apply (h_1_34_s7 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  have s8_a1 : ∠ a:b:c = ∠ b:c:d := by assumption

  have s8_a2 : ∠ c:b:d = ∠ a:c:b := by linarith

  have s8 : ∠ a:b:d = ∠ a:c:d := by euclid_apply (h_1_34_s8 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)) (by (show ∠ a:c:b = ∠ c:b:d; assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)) (by (show ∠ c:b:d = ∠ a:c:b; assumption)))

  have s9 : ∠ b:a:c = ∠ c:d:b := by euclid_apply (h_1_34_s9 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  have s10 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b := by euclid_apply (h_1_34_s10 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)|; assumption)) (by (show |(a─c)| = |(b─d)|; assumption)) (by (show ∠ a:b:d = ∠ a:c:d; assumption)) (by (show ∠ b:a:c = ∠ c:d:b; assumption)))

  have s12 : |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)| := by euclid_apply (h_1_34_s12 a b c d AB CD AC BD BC (by (show |(a─b)| = |(c─d)|; assumption)))

  have s13 : ∠ a:b:c = ∠ b:c:d := by euclid_apply (h_1_34_s13 a b c d AB CD AC BD BC (by (show ∠ a:b:c = ∠ b:c:d; assumption)))

  have s14 : |(a─c)| = |(d─b)| := by euclid_apply (h_1_34_s14 a b c d AB CD AC BD BC (by (show |(a─c)| = |(b─d)|; assumption)))

  have s15 : Triangle.area △ a:b:c = Triangle.area △ b:c:d := by euclid_apply (h_1_34_s15 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show b ≠ c; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show ¬(AC.intersectsLine BD); assumption)) (by (show formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD; assumption)) (by (show |(a─b)| = |(c─d)|; assumption)) (by (show ∠ b:a:c = ∠ c:d:b; assumption)) (by (show |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|; assumption)) (by (show |(a─c)| = |(d─b)|; assumption)))

  have s16 : Triangle.area △ a:b:c = Triangle.area △ d:c:b := by euclid_apply (h_1_34_s16 a b c d AB CD AC BD BC (by (show Triangle.area △ a:b:c = Triangle.area △ b:c:d; assumption)))

  exact ⟨s5, s6, s8, s7, s16⟩

end Elements.Book1
