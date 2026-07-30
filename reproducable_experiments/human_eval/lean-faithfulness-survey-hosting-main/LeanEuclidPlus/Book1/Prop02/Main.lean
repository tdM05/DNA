import SystemE
import Book1Variants.Prop01
import Book1.Prop02.step1
import Book1.Prop02.step2
import Book1.Prop02.step3
import Book1.Prop02.step4
import Book1.Prop02.step5
import Book1.Prop02.step6
import Book1.Prop02.step7
import Book1.Prop02.step8
import Book1.Prop02.step9
import Book1.Prop02.step10
import Book1.Prop02.step11
import Book1.Prop02.step12
import Book1.Prop02.step13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_2 : ∀ (a b c : Point) (BC : Line),
  (distinctPointsOnLine b c BC) ∧ (a ≠ b) →
  ∃ l : Point, |(a─l)| = |(b─c)| := by
  euclid_intros

  euclid_apply (line_from_points a b) as AB
  have s1 : distinctPointsOnLine a b AB := by euclid_apply (h_1_2_s1 a b AB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)))

  euclid_apply (proposition_1 a b AB) as d
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points d b) as DB
  have s2 : formTriangle d a b DA AB DB ∧ |(d─a)| = |(a─b)| ∧ |(d─b)| = |(a─b)| := by euclid_apply (h_1_2_s2 d a b DA AB DB (by (show d.onLine DA; assumption)) (by (show a.onLine DA; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show |(d─a)| = |(a─b)|; assumption)) (by (show |(d─b)| = |(a─b)|; assumption)) (by (show a ≠ b; assumption)))

  euclid_apply (extend_point DA d a) as e
  euclid_apply (extend_point DB d b) as f
  have s3 : between d a e ∧ between d b f := by euclid_apply (h_1_2_s3 d a b e f (by (show between d a e; assumption)) (by (show between d b f; assumption)))

  euclid_apply (circle_from_points b c) as CGH
  have s4 : b.isCentre CGH ∧ c.onCircle CGH := by euclid_apply (h_1_2_s4 b c CGH (by (show b.isCentre CGH; assumption)) (by (show c.onCircle CGH; assumption)))

  euclid_apply (intersection_circle_line_extending_points CGH DB b d) as g
  euclid_apply (circle_from_points d g) as GKL
  have s5 : d.isCentre GKL ∧ g.onCircle GKL := by euclid_apply (h_1_2_s5 d g GKL (by (show d.isCentre GKL; assumption)) (by (show g.onCircle GKL; assumption)))

  euclid_apply (intersection_circle_line_extending_points GKL DA a d) as l

  have s6_a1 : b.isCentre CGH := by assumption

  have s6 : |(b─c)| = |(b─g)| := by euclid_apply (h_1_2_s6 b c g CGH (by (show b.isCentre CGH; assumption)) (by (show c.onCircle CGH; assumption)) (by (show g.onCircle CGH; assumption)))

  have s7_a1 : d.isCentre GKL := by assumption

  have s7 : |(d─l)| = |(d─g)| := by euclid_apply (h_1_2_s7 d l g GKL (by (show d.isCentre GKL; assumption)) (by (show l.onCircle GKL; assumption)) (by (show g.onCircle GKL; assumption)))

  have s8 : |(d─a)| = |(d─b)| := by euclid_apply (h_1_2_s8 d a b (by (show |(d─a)| = |(a─b)|; assumption)) (by (show |(d─b)| = |(a─b)|; assumption)))

  have s9 : |(a─l)| = |(b─g)| := by euclid_apply (h_1_2_s9 d a b g l (by (show |(d─l)| = |(d─g)|; assumption)) (by (show |(d─a)| = |(d─b)|; assumption)) (by (show between l a d; assumption)) (by (show between g b d; assumption)))

  have s10 : |(b─c)| = |(b─g)| := by euclid_apply (h_1_2_s10 b c g (by (show |(b─c)| = |(b─g)|; assumption)))

  have s11 : |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)| := by euclid_apply (h_1_2_s11 a l b c g (by (show |(a─l)| = |(b─g)|; assumption)) (by (show |(b─c)| = |(b─g)|; assumption)))

  have s12 : (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)| := by euclid_apply (h_1_2_s12 a l b c g)

  have s13 : |(a─l)| = |(b─c)| := by euclid_apply (h_1_2_s13 a l b c g (by (show |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|; assumption)) (by (show (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)|; assumption)))

  exact ⟨l, s13⟩

end Elements.Book1
