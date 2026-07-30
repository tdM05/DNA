import SystemE
import Book1Variants.Prop01
import Book1Variants.Prop09
import Book1.Prop10.step1
import Book1.Prop10.step2
import Book1.Prop10.step4
import Book1.Prop10.step5
import Book1.Prop10.step6
import Book1.Prop10.hbet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_10 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) := by
  euclid_intros

  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b) as BC
  have s1 : formTriangle a b c AB BC AC ∧ |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by euclid_apply (h_1_10_s1 a b c AB AC BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show |(c─a)| = |(a─b)|; assumption)) (by (show |(c─b)| = |(a─b)|; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)))

  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  euclid_apply (intersection_lines CD AB) as d
  have s2 : ∠ a:c:d = ∠ b:c:d := by euclid_apply (h_1_10_s2 a b c d d' AB AC BC CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d'.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show d'.sameSide b AC; assumption)) (by (show d'.sameSide a BC; assumption)) (by (show ∠ a:c:d' = ∠ b:c:d'; assumption)))

  have s4_a1 : |(a─c)| = |(c─b)| := by euclid_finish

  have s4_a2 : |(c─d)| = |(c─d)| := by rfl

  have s4 : |(a─c)| = |(b─c)| ∧ |(c─d)| = |(c─d)| := by euclid_apply (h_1_10_s4 a b c d (by (show |(a─c)| = |(c─b)|; assumption)) (by (show |(c─d)| = |(c─d)|; assumption)))

  have s5 : ∠ a:c:d = ∠ b:c:d := by euclid_apply (h_1_10_s5 a b c d d' AB AC BC CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d'.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show d'.sameSide b AC; assumption)) (by (show d'.sameSide a BC; assumption)) (by (show ∠ a:c:d' = ∠ b:c:d'; assumption)))

  have s6 : |(a─d)| = |(d─b)| := by euclid_apply (h_1_10_s6 a b c d d' AB AC BC CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show d'.onLine CD; assumption)) (by (show d'.sameSide b AC; assumption)) (by (show d'.sameSide a BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show |(c─a)| = |(a─b)|; assumption)) (by (show |(c─b)| = |(a─b)|; assumption)) (by (show ∠ a:c:d = ∠ b:c:d; assumption)))

  have hbet : between a d b := by euclid_apply (h_1_10_x1 a b c d d' AB AC BC CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show d'.onLine CD; assumption)) (by (show d.onLine AB; assumption)) (by (show d'.sameSide b AC; assumption)) (by (show d'.sameSide a BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show |(c─a)| = |(a─b)|; assumption)) (by (show |(c─b)| = |(a─b)|; assumption)) (by (show |(a─d)| = |(d─b)|; assumption)))
  exact ⟨d, hbet, s6⟩

end Elements.Book1
