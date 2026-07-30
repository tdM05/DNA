import SystemE
import Book1.Prop33.step1
import Book1.Prop33.step2
import Book1.Prop33.step3
import Book1.Prop33.step4
import Book1.Prop33.step5
import Book1.Prop33.step6
import Book1.Prop33.step7
import Book1.Prop33.step8
import Book1.Prop33.step9
import Book1.Prop33.hAC_BD
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_33 : ∀ (a b c d : Point) (AB CD AC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ |(a─b)| = |(c─d)| →
  AC ≠ BD ∧ ¬(AC.intersectsLine BD) ∧ |(a─c)|= |(b─d)| := by
  euclid_intros

  euclid_apply (line_from_points b c) as BC
  have s1 : distinctPointsOnLine b c BC := by euclid_apply (h_1_33_s1 a b c AC BD BC (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BD; assumption)) (by (show a.sameSide c BD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)))

  have s2_a1 : ¬(AB.intersectsLine CD) := by assumption

  have s2_a2 : distinctPointsOnLine b c BC := by assumption

  have s2 : ∠ a:b:c = ∠ b:c:d := by euclid_apply (h_1_33_s2 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show distinctPointsOnLine b c BC; assumption)))

  have s3_a1 : |(a─b)| = |(c─d)| := by assumption

  have s3_a2 : |(b─c)| = |(b─c)| := by rfl

  have s3 : (|(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) ∧ ∠ a:b:c = ∠ b:c:d := by euclid_apply (h_1_33_s3 a b c d (by (show |(a─b)| = |(c─d)|; assumption)) (by (show |(b─c)| = |(b─c)|; assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)))

  have s4 : |(a─c)| = |(b─d)| := by euclid_apply (h_1_33_s4 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show |(a─b)| = |(c─d)|; assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)))

  have s5 : Triangle.area △ a:b:c = Triangle.area △ d:c:b := by euclid_apply (h_1_33_s5 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show |(a─b)| = |(c─d)|; assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)))

  have s6 : ∠ b:a:c = ∠ c:d:b ∧ ∠ a:c:b = ∠ d:b:c := by euclid_apply (h_1_33_s6 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show |(a─b)| = |(c─d)|; assumption)) (by (show ∠ a:b:c = ∠ b:c:d; assumption)))

  have s7 : ∠ a:c:b = ∠ c:b:d := by euclid_apply (h_1_33_s7 a b c d BC (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ d; assumption)) (by (show distinctPointsOnLine b c BC; assumption)) (by (show ∠ b:a:c = ∠ c:d:b ∧ ∠ a:c:b = ∠ d:b:c; assumption)))

  have s8_a1 : ∠ a:c:b = ∠ c:b:d := by assumption

  have s8 : ¬(AC.intersectsLine BD) := by euclid_apply (h_1_33_s8 a b c d AB CD AC BD BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.sameSide c BD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)) (by (show distinctPointsOnLine b c BC; assumption)) (by (show ∠ a:c:b = ∠ c:b:d; assumption)))

  have s9 : |(a─c)| = |(b─d)| := by euclid_apply (h_1_33_s9 a b c d (by (show |(a─c)| = |(b─d)|; assumption)))

  have hAC_BD : AC ≠ BD := by euclid_apply (h_1_33_x1 a b c AC BD (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BD; assumption)) (by (show a.sameSide c BD; assumption)))
  exact ⟨hAC_BD, s8, s9⟩

end Elements.Book1
