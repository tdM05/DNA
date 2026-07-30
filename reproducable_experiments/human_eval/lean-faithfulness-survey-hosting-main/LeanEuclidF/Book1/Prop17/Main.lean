import SystemE
import Book1.Prop17.step1
import Book1.Prop17.step2
import Book1.Prop17.step3
import Book1.Prop17.step4
import Book1.Prop17.step5
import Book1.Prop17.step6
import Book1.Prop17.step7
import Book1.Prop17.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_17 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ := by
  euclid_intros

  euclid_apply (extend_point BC b c) as d
  have s1 : between b c d := by euclid_apply (h_1_17_s1 b c d (by (show between b c d; assumption)))

  have s2_a1 : between b c d := by assumption

  have s2 : ∠ a:c:d > ∠ a:b:c := by euclid_apply (h_1_17_s2 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BC; assumption)) (by (show between b c d; assumption)))

  have s3 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b := by euclid_apply (h_1_17_s3 a b c d (by (show ∠ a:c:d > ∠ a:b:c; assumption)))

  have s4 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a := by euclid_apply (h_1_17_s4 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b; assumption)))

  have s5 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟ := by euclid_apply (h_1_17_s5 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BC; assumption)) (by (show between b c d; assumption)))

  have s6 : ∠ a:b:c + ∠ b:c:a < ∟ + ∟ := by euclid_apply (h_1_17_s6 a b c d (by (show ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a; assumption)) (by (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  have s7 : ∠ b:a:c + ∠ a:c:b < ∟ + ∟ := by euclid_apply (h_1_17_s7 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BC; assumption)) (by (show between b c d; assumption)) (by (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  have s8 : ∠ c:a:b + ∠ a:b:c < ∟ + ∟ := by euclid_apply (h_1_17_s8 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)))

  exact s6

end Elements.Book1
