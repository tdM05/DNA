import SystemE
import Book1.Prop10.Main
import Book1.Prop12.step1
import Book1.Prop12.step2
import Book1.Prop12.step3
import Book1.Prop12.step4
import Book1.Prop12.step6
import Book1.Prop12.step7
import Book1.Prop12.step8
import Book1.Prop12.step9
import Book1.Prop12.step10
import Book1.Prop12.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) := by
  euclid_intros

  euclid_apply (exists_point_opposite AB c) as d
  have s1 : d.opposingSides c AB := by euclid_apply (h_1_12_s1 d c AB (by (show ¬d.onLine AB; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show ¬d.sameSide c AB; assumption)))

  euclid_apply (circle_from_points c d) as EFG
  euclid_apply (intersections_circle_line EFG AB) as (e, g)
  have s2 : c.isCentre EFG ∧ d.onCircle EFG := by euclid_apply (h_1_12_s2 c d EFG (by (show c.isCentre EFG; assumption)) (by (show d.onCircle EFG; assumption)))

  euclid_apply (proposition_10 e g AB) as h
  have s3 : between e h g ∧ |(e─h)| = |(h─g)| := by euclid_apply (h_1_12_s3 e h g (by (show between e h g; assumption)) (by (show |(e─h)| = |(h─g)|; assumption)))

  euclid_apply (line_from_points c g) as CG
  euclid_apply (line_from_points c h) as CH
  euclid_apply (line_from_points c e) as CE
  have s4 : distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE := by euclid_apply (h_1_12_s4 c e g h AB CG CH CE (by (show ¬c.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show g.onLine AB; assumption)) (by (show between e h g; assumption)) (by (show c.onLine CG; assumption)) (by (show g.onLine CG; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)))

  have s6_a1 : |(g─h)| = |(h─e)| := by euclid_finish

  have s6_a2 : |(h─c)| = |(h─c)| := by rfl

  have s6 : |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)| := by euclid_apply (h_1_12_s6 g h e c (by (show |(g─h)| = |(h─e)|; assumption)) (by (show |(h─c)| = |(h─c)|; assumption)))

  have s7 : |(c─g)| = |(c─e)| := by euclid_apply (h_1_12_s7 c e g EFG (by (show c.isCentre EFG; assumption)) (by (show e.onCircle EFG; assumption)) (by (show g.onCircle EFG; assumption)))

  have s8 : ∠ c:h:g = ∠ e:h:c := by euclid_apply (h_1_12_s8 c e g h AB CG CH CE EFG (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show c.onLine CG; assumption)) (by (show g.onLine CG; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show e.onLine AB; assumption)) (by (show g.onLine AB; assumption)) (by (show between e h g; assumption)) (by (show c.isCentre EFG; assumption)) (by (show e.onCircle EFG; assumption)) (by (show g.onCircle EFG; assumption)) (by (show distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show |(g─h)| = |(h─e)|; assumption)) (by (show |(c─g)| = |(c─e)|; assumption)))

  have s9 : h.onLine AB := by euclid_apply (h_1_12_s9 e h g AB (by (show between e h g; assumption)) (by (show e.onLine AB; assumption)) (by (show g.onLine AB; assumption)))

  have s10_a1 : ∠ c:h:g = ∠ e:h:c := by assumption

  have s10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟ := by euclid_apply (h_1_12_s10 c e g h AB (by (show e.onLine AB; assumption)) (by (show g.onLine AB; assumption)) (by (show h.onLine AB; assumption)) (by (show between e h g; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show ∠ c:h:g = ∠ e:h:c; assumption)))

  have s11 : ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by euclid_apply (h_1_12_s11 a b c e g h AB CH (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show g.onLine AB; assumption)) (by (show h.onLine AB; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show between e h g; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟; assumption)))

  exact ⟨h, s9, s11⟩

end Elements.Book1
