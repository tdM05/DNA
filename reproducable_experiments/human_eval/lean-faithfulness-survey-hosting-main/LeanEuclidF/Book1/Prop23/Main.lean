import SystemE
import Book1.Prop20.Main
import Book1Variants.Prop22
import Book1.Prop23.step1
import Book1.Prop23.step2
import Book1.Prop23.step3
import Book1.Prop23.step4
import Book1.Prop23.step5
import Book1.Prop23.step6
import Book1.Prop23.hfoff
import Book1.Prop23.hfa
import Book1.Prop23.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) := by
  euclid_intros

  by_cases (d.onLine CE)

  ·
    by_cases (∠ d:c:e = 0)
    · use b; euclid_finish
    · euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'; euclid_finish
  euclid_apply (line_from_points d e) as DE
  have s1 : distinctPointsOnLine d e DE := by euclid_apply (h_1_23_s1 d e CE DE (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬d.onLine CE; assumption)))

  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as FA
  euclid_apply (line_from_points f g) as FG
  have hfoff : ¬f.onLine AB := by euclid_apply (h_1_23_x3 c d e a b f g AB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show g.onLine AB; assumption)) (by (show |(a─f)| = |(c─d)|; assumption)) (by (show |(a─g)| = |(c─e)|; assumption)) (by (show |(f─g)| = |(e─d)|; assumption)) (by (show |(d─c)| + |(c─e)| > |(d─e)|; assumption)) (by (show |(e─d)| + |(d─c)| > |(e─c)|; assumption)) (by (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))
  have s2 : formTriangle a f g FA FG AB := by euclid_apply (h_1_23_s2 a b f g AB FA FG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show g.onLine AB; assumption)) (by (show ¬between g a b; assumption)) (by (show a.onLine FA; assumption)) (by (show f.onLine FA; assumption)) (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show |(a─f)| = |(c─d)|; assumption)) (by (show |(a─g)| = |(c─e)|; assumption)) (by (show |(f─g)| = |(e─d)|; assumption)) (by (show |(d─c)| + |(c─e)| > |(d─e)|; assumption)) (by (show |(e─d)| + |(d─c)| > |(e─c)|; assumption)) (by (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))
  have s3 : |(c─d)| = |(a─f)| := by euclid_apply (h_1_23_s3 c d a f (by (show |(a─f)| = |(c─d)|; assumption)))
  have s4 : |(c─e)| = |(a─g)| := by euclid_apply (h_1_23_s4 c e a g (by (show |(a─g)| = |(c─e)|; assumption)))
  have s5 : |(d─e)| = |(f─g)| := by euclid_apply (h_1_23_s5 d e f g (by (show |(f─g)| = |(e─d)|; assumption)))

  have s6_a1 : |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)| := by euclid_finish

  have s6_a2 : |(d─e)| = |(f─g)| := by assumption

  have s6 : ∠ d:c:e = ∠ f:a:g := by euclid_apply (h_1_23_s6 c d e a f g CD CE DE FA FG AB (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show ¬d.onLine CE; assumption)) (by (show formTriangle a f g FA FG AB; assumption)) (by (show |(c─d)| = |(a─f)|; assumption)) (by (show |(c─e)| = |(a─g)|; assumption)) (by (show |(d─e)| = |(f─g)|; assumption)) (by (show |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)|; assumption)) (by (show |(d─e)| = |(f─g)|; assumption)))
  use f
  have hfa : f ≠ a := by euclid_apply (h_1_23_x2 a f AB (by (show a.onLine AB; assumption)) (by (show ¬f.onLine AB; assumption)))
  have hangle : ∠ f:a:b = ∠ d:c:e := by euclid_apply (h_1_23_x1 a b f g AB FA (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show g.onLine AB; assumption)) (by (show a.onLine FA; assumption)) (by (show f.onLine FA; assumption)) (by (show ¬f.onLine AB; assumption)) (by (show f ≠ a; assumption)) (by (show a ≠ b; assumption)) (by (show ¬between g a b; assumption)) (by (show |(a─g)| = |(c─e)|; assumption)) (by (show c ≠ e; assumption)) (by (show ∠ d:c:e = ∠ f:a:g; assumption)))
  exact ⟨hfa, hangle⟩

end Elements.Book1
