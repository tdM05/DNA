import SystemE
import Book1Variants.Prop02
import Book1.Prop03.step1
import Book1.Prop03.step2
import Book1.Prop03.step3
import Book1.Prop03.step4
import Book1.Prop03.step5
import Book1.Prop03.step6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_3 : ∀ (a b c₀ c₁ : Point) (AB C : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| →
  ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)| := by
  euclid_intros

  euclid_apply (proposition_2' a c₀ c₁ C) as d
  have s1 : |(a─d)| = |(c₀─c₁)| := by euclid_apply (h_1_3_s1 a d c₀ c₁ (by (show |(a─d)| = |(c₀─c₁)|; assumption)))

  euclid_apply (circle_from_points a d) as DEF
  euclid_apply (intersection_circle_line_between_points DEF AB a b) as e
  have s2 : a.isCentre DEF ∧ d.onCircle DEF := by euclid_apply (h_1_3_s2 a d DEF (by (show a.isCentre DEF; assumption)) (by (show d.onCircle DEF; assumption)))

  have s3_a1 : a.isCentre DEF := by assumption

  have s3 : |(a─e)| = |(a─d)| := by euclid_apply (h_1_3_s3 a d e DEF (by (show a.isCentre DEF; assumption)) (by (show d.onCircle DEF; assumption)) (by (show e.onCircle DEF; assumption)))

  have s4 : |(c₀─c₁)| = |(a─d)| := by euclid_apply (h_1_3_s4 a d c₀ c₁ (by (show |(a─d)| = |(c₀─c₁)|; assumption)))

  have s5 : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)| := by euclid_apply (h_1_3_s5 a d e c₀ c₁ (by (show |(a─e)| = |(a─d)|; assumption)) (by (show |(c₀─c₁)| = |(a─d)|; assumption)))

  have s6 : |(a─e)| = |(c₀─c₁)| := by euclid_apply (h_1_3_s6 a d e c₀ c₁ (by (show |(a─e)| = |(a─d)|; assumption)) (by (show |(c₀─c₁)| = |(a─d)|; assumption)))

  use e

end Elements.Book1
