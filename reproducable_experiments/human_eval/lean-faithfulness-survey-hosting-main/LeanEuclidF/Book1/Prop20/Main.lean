import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step1
import Book1.Prop20.step2
import Book1.Prop20.step3
import Book1.Prop20.step4
import Book1.Prop20.step5
import Book1.Prop20.step6
import Book1.Prop20.step7
import Book1.Prop20.step8
import Book1.Prop20.step9
import Book1.Prop20.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  |(b─a)| + |(a─c)| > |(b─c)| ∧
  |(a─b)| + |(b─c)| > |(a─c)| ∧
  |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_intros

  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  have s1 : between b a d := by euclid_apply (h_1_20_s1 b a d d' AB (by (show b.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show d'.onLine AB; assumption)) (by (show between b a d'; assumption)) (by (show between a d d'; assumption)))

  have s2 : |(a─d)| = |(c─a)| := by euclid_apply (h_1_20_s2 a c d (by (show |(a─d)| = |(a─c)|; assumption)))

  euclid_apply (line_from_points d c) as DC
  have s3 : distinctPointsOnLine d c DC := by euclid_apply (h_1_20_s3 a b c d d' AB BC DC (by (show AB ≠ BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d'.onLine AB; assumption)) (by (show between a d d'; assumption)) (by (show between b a d; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)))

  have s4_a1 : |(d─a)| = |(a─c)| := by euclid_finish

  have s4 : ∠ a:d:c = ∠ a:c:d := by euclid_apply (h_1_20_s4 a b c d d' AB BC AC DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d'.onLine AB; assumption)) (by (show between a d d'; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show |(d─a)| = |(a─c)|; assumption)))

  have s5 : ∠ b:c:d > ∠ a:d:c := by euclid_apply (h_1_20_s5 a b c d d' AB BC AC DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d'.onLine AB; assumption)) (by (show between a d d'; assumption)) (by (show between b a d; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show ∠ a:d:c = ∠ a:c:d; assumption)))

  have s6_a1 : ∠ b:c:d > ∠ b:d:c := by euclid_finish

  have s6 : |(d─b)| > |(b─c)| := by euclid_apply (h_1_20_s6 a b c d d' AB BC AC DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d'.onLine AB; assumption)) (by (show between a d d'; assumption)) (by (show between b a d; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show ∠ b:c:d > ∠ b:d:c; assumption)))

  have s7 : |(d─a)| = |(a─c)| := by euclid_apply (h_1_20_s7 a c d (by (show |(d─a)| = |(a─c)|; assumption)))

  have s8 : |(b─a)| + |(a─c)| > |(b─c)| := by euclid_apply (h_1_20_s8 a b c d (by (show between b a d; assumption)) (by (show |(d─b)| > |(b─c)|; assumption)) (by (show |(d─a)| = |(a─c)|; assumption)))

  have s9 : |(a─b)| + |(b─c)| > |(a─c)| := by euclid_apply (h_1_20_s9 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a ≠ b; assumption)))

  have s10 : |(b─c)| + |(c─a)| > |(a─b)| := by euclid_apply (h_1_20_s10 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a ≠ b; assumption)))

  exact ⟨s8, s9, s10⟩

end Elements.Book1
