import SystemE
import Book1.Prop01.step1
import Book1.Prop01.step2
import Book1.Prop01.step3
import Book1.Prop01.step4
import Book1.Prop01.step5
import Book1.Prop01.step6
import Book1.Prop01.step7
import Book1.Prop01.step8
import Book1.Prop01.step9
import Book1.Prop01.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
  euclid_intros

  euclid_apply (circle_from_points a b) as BCD
  have s1 : a.isCentre BCD ∧ b.onCircle BCD := by euclid_apply (h_1_1_s1 a b BCD (by (show a.isCentre BCD; assumption)) (by (show b.onCircle BCD; assumption)))

  euclid_apply (circle_from_points b a) as ACE
  have s2 : b.isCentre ACE ∧ a.onCircle ACE := by euclid_apply (h_1_1_s2 a b ACE (by (show b.isCentre ACE; assumption)) (by (show a.onCircle ACE; assumption)))

  euclid_apply (intersection_circles BCD ACE) as c
  euclid_apply (line_from_points c a) as CA
  euclid_apply (line_from_points c b) as CB
  have s3 : distinctPointsOnLine c a CA ∧ distinctPointsOnLine c b CB := by euclid_apply (h_1_1_s3 a b c CA CB BCD ACE (by (show c.onLine CA; assumption)) (by (show a.onLine CA; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show a.isCentre BCD; assumption)) (by (show c.onCircle BCD; assumption)) (by (show b.isCentre ACE; assumption)) (by (show c.onCircle ACE; assumption)))

  have s4_a1 : a.isCentre BCD := by assumption

  have s4 : |(a─c)| = |(a─b)| := by euclid_apply (h_1_1_s4 a b c BCD (by (show a.isCentre BCD; assumption)) (by (show b.onCircle BCD; assumption)) (by (show c.onCircle BCD; assumption)))

  have s5_a1 : b.isCentre ACE := by assumption

  have s5 : |(b─c)| = |(b─a)| := by euclid_apply (h_1_1_s5 a b c ACE (by (show b.isCentre ACE; assumption)) (by (show a.onCircle ACE; assumption)) (by (show c.onCircle ACE; assumption)))

  have s6 : |(c─a)| = |(a─b)| := by euclid_apply (h_1_1_s6 a b c (by (show |(a─c)| = |(a─b)|; assumption)))

  have s7 : |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by euclid_apply (h_1_1_s7 a b c (by (show |(c─a)| = |(a─b)|; assumption)) (by (show |(b─c)| = |(b─a)|; assumption)))

  have s8 : (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)| := by euclid_apply (h_1_1_s8 a b c)

  have s9 : |(c─a)| = |(c─b)| := by euclid_apply (h_1_1_s9 a b c (by (show |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|; assumption)) (by (show (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)|; assumption)))

  have s10 : |(c─a)| = |(a─b)| ∧ |(a─b)| = |(b─c)| := by euclid_apply (h_1_1_s10 a b c (by (show |(c─a)| = |(a─b)|; assumption)) (by (show |(b─c)| = |(b─a)|; assumption)))

  exact ⟨c, s7⟩

end Elements.Book1
