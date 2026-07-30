import SystemE
import Book1.Prop21.step1
import Book1.Prop21.step2
import Book1.Prop21.step3
import Book1.Prop21.step4
import Book1.Prop21.step5
import Book1.Prop21.step6
import Book1.Prop21.step7
import Book1.Prop21.step8
import Book1.Prop21.step9
import Book1.Prop21.step10
import Book1.Prop21.step11
import Book1.Prop21.step12
import Book1.Prop21.step5_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_21 : ∀ (a b c d : Point) (AB BC AC BD DC : Line),
  formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC →
  (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c) := by
  euclid_intros

  euclid_apply (intersection_lines BD AC) as e
  have s1 : between b d e ∧ e.onLine BD := by euclid_apply (h_1_21_s1 a b c d e AB BC AC BD DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)))

  have s2 : |(a─b)| + |(a─e)| > |(b─e)| := by euclid_apply (h_1_21_s2 a b c d e AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)))

  have s3 : |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)| := by euclid_apply (h_1_21_s3 a b c e (by (show |(a─b)| + |(a─e)| > |(b─e)|; assumption)))

  have s4 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)| := by euclid_apply (h_1_21_s4 a b c d e AB BC AC BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)) (by (show between b d e ∧ e.onLine BD; assumption)) (by (show |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)|; assumption)))

  have s5_a1 : |(c─e)| + |(e─d)| > |(c─d)| := by euclid_apply (h_1_21_s5_x1 a b c d e AB BC AC BD DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)))

  have s5 : |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)| := by euclid_apply (h_1_21_s5 b c d e (by (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))

  have s6 : |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)| := by euclid_apply (h_1_21_s6 b c d e (by (show between b d e ∧ e.onLine BD; assumption)) (by (show |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)|; assumption)))

  have s7 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)| := by euclid_apply (h_1_21_s7 a b c e (by (show |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|; assumption)))

  have s8 : |(b─a)| + |(a─c)| > |(b─d)| + |(d─c)| := by euclid_apply (h_1_21_s8 a b c d e (by (show |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|; assumption)) (by (show |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)|; assumption)))

  have s9 : ∠ b:d:c > ∠ c:e:d := by euclid_apply (h_1_21_s9 a b c d e AB BC AC BD DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)) (by (show between b d e ∧ e.onLine BD; assumption)))

  have s10 : ∠ c:e:b > ∠ b:a:c := by euclid_apply (h_1_21_s10 a b c d e AB BC AC BD DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)) (by (show between b d e ∧ e.onLine BD; assumption)))

  have s11 : ∠ b:d:c > ∠ c:e:b := by euclid_apply (h_1_21_s11 a b c d e AB BC AC BD DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine BD; assumption)) (by (show e.onLine AC; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show b.sameSide d AC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show c.sameSide d AB; assumption)) (by (show between b d e ∧ e.onLine BD; assumption)) (by (show ∠ b:d:c > ∠ c:e:d; assumption)))

  have s12 : ∠ b:d:c > ∠ b:a:c := by euclid_apply (h_1_21_s12 a b c d e (by (show ∠ c:e:b > ∠ b:a:c; assumption)) (by (show ∠ b:d:c > ∠ c:e:b; assumption)))

  exact ⟨s8, s12⟩

end Elements.Book1
