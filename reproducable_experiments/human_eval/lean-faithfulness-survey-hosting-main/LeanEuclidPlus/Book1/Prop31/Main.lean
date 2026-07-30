import SystemE
import Book1Variants.Prop23
import Book1.Prop27.Main
import Book1.Prop31.step1
import Book1.Prop31.step2
import Book1.Prop31.step3
import Book1.Prop31.step4
import Book1.Prop31.step5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_31 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC) := by
  euclid_intros

  euclid_apply (exists_point_between_points_on_line BC b c) as d
  have s1 : d.onLine BC := by euclid_apply (h_1_31_s1 d BC (by (show d.onLine BC; assumption)))

  euclid_apply (line_from_points a d) as AD
  have s2 : distinctPointsOnLine a d AD := by euclid_apply (h_1_31_s2 a d BC AD (by (show ¬a.onLine BC; assumption)) (by (show d.onLine BC; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)))

  euclid_apply (proposition_23' a d d a c b AD AD BC) as e
  have s3 : ∠ d:a:e = ∠ a:d:c := by euclid_apply (h_1_31_s3 a d e c AD BC (by (show e ≠ a; assumption)) (by (show a ≠ d; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show ∠ e:a:d = ∠ a:d:c; assumption)))

  euclid_apply (line_from_points e a) as EF
  euclid_apply (extend_point EF e a) as f
  have s4 : between e a f := by euclid_apply (h_1_31_s4 e a f (by (show between e a f; assumption)))

  have s5_a1 : ∠ e:a:d = ∠ a:d:c := by assumption

  have s5 : ¬(EF.intersectsLine BC) := by euclid_apply (h_1_31_s5 a b c d e EF BC AD (by (show e.onLine EF; assumption)) (by (show a.onLine EF; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show e ≠ a; assumption)) (by (show a ≠ d; assumption)) (by (show between b d c; assumption)) (by (show e.onLine AD ∨ e.sameSide b AD; assumption)) (by (show ∠ e:a:d = ∠ a:d:c; assumption)))

  use EF

end Elements.Book1
