import SystemE
import Book1.Prop07.step1
import Book1.Prop07.step2
import Book1.Prop07.step3
import Book1.Prop07.step4
import Book1.Prop07.step5
import Book1.Prop07.step6
import Book1.Prop07.step7
import Book1.Prop07.step8
import Book1.Prop07.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_7 : ∀ (a b c d : Point) (AB AC CB AD DB : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧
  (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False := by
  euclid_intros

  have s1 : |(c─a)| = |(d─a)| := by euclid_apply (h_1_7_s1 a c d (by (show |(a─c)| = |(a─d)|; assumption)))

  have s2 : |(c─b)| = |(d─b)| := by euclid_apply (h_1_7_s2 c d b (by (show |(c─b)| = |(d─b)|; assumption)))

  euclid_apply (line_from_points c d) as CD
  have s3 : c.onLine CD ∧ d.onLine CD := by euclid_apply (h_1_7_s3 c d CD (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)))

  have s4_a1 : |(a─c)| = |(a─d)| := by assumption

  have s4 : ∠ a:c:d = ∠ a:d:c := by euclid_apply (h_1_7_s4 a c d AB AC CD AD (by (show a.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show c ≠ d; assumption)) (by (show c.sameSide d AB; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)))

  have s5 : ∠ a:d:c > ∠ d:c:b := by euclid_apply (h_1_7_s5 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)))

  have s6 : ∠ c:d:b > ∠ d:c:b := by euclid_apply (h_1_7_s6 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:d:c > ∠ d:c:b; assumption)))

  have s7_a1 : |(c─b)| = |(d─b)| := by assumption

  have s7 : ∠ c:d:b = ∠ d:c:b := by euclid_apply (h_1_7_s7 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)))

  have s8 : ∠ c:d:b > ∠ d:c:b := by euclid_apply (h_1_7_s8 c d b (by (show ∠ c:d:b > ∠ d:c:b; assumption)))

  have s9 : False := by euclid_apply (h_1_7_s9 c d b (by (show ∠ c:d:b = ∠ d:c:b; assumption)) (by (show ∠ c:d:b > ∠ d:c:b; assumption)))

  exact s9

end Elements.Book1
