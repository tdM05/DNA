import SystemE
import Book1Variants.Prop01
import Book1.Prop03.Main
import Mathlib.Tactic.Linarith
import Book1.Prop09.step1
import Book1.Prop09.step2
import Book1.Prop09.step3
import Book1.Prop09.step4
import Book1.Prop09.step5
import Book1.Prop09.step7
import Book1.Prop09.step8
import Book1.Prop09.step9
import Book1.Prop09.hfa
import Book1.Prop09.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) := by
  euclid_intros

  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  have s1 : between a d b := by euclid_apply (h_1_9_s1 a b d (by (show between a d b; assumption)))

  euclid_apply (proposition_3 a c a d AC AB) as e
  have s2 : between a e c ∧ |(a─e)| = |(a─d)| := by euclid_apply (h_1_9_s2 a c d e (by (show between a e c; assumption)) (by (show |(a─e)| = |(a─d)|; assumption)))

  euclid_apply (line_from_points d e) as DE
  have s3 : distinctPointsOnLine d e DE := by euclid_apply (h_1_9_s3 a b c d e AB AC DE (by (show AB ≠ AC; assumption)) (by (show a.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show between a d b; assumption)) (by (show between a e c; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)))

  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points d f) as DF
  have s4 : formTriangle d e f DE EF DF ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by euclid_apply (h_1_9_s4 d e f DE EF DF (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show ¬f.onLine DE; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))

  euclid_apply (line_from_points a f) as AF
  have s5 : distinctPointsOnLine a f AF := by euclid_apply (h_1_9_s5 a f DE AF (by (show a.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show ¬f.onLine DE; assumption)) (by (show ¬a.onLine DE; assumption)) (by (show ¬f.sameSide a DE; assumption)))

  have s7_a1 : |(a─d)| = |(a─e)| := by linarith

  have s7_a2 : |(a─f)| = |(a─f)| := by rfl

  have s7 : |(d─a)| = |(e─a)| ∧ |(a─f)| = |(a─f)| := by euclid_apply (h_1_9_s7 a d e f (by (show |(a─d)| = |(a─e)|; assumption)) (by (show |(a─f)| = |(a─f)|; assumption)))

  have s8 : |(d─f)| = |(e─f)| := by euclid_apply (h_1_9_s8 d e f (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))

  have s9 : ∠ d:a:f = ∠ e:a:f := by euclid_apply (h_1_9_s9 a b c d e f AB AC DE EF DF AF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show between a d b; assumption)) (by (show between a e c; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show a.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show ¬f.onLine DE; assumption)) (by (show ¬a.onLine DE; assumption)) (by (show ¬f.sameSide a DE; assumption)) (by (show AB ≠ AC; assumption)) (by (show |(a─d)| = |(a─e)|; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show |(d─f)| = |(e─f)|; assumption)))

  use f
  have hfa : f ≠ a := by euclid_apply (h_1_9_x2 a f AF (by (show distinctPointsOnLine a f AF; assumption)))
  have hangle : ∠ b:a:f = ∠ c:a:f := by euclid_apply (h_1_9_x1 a b c d e f AB AC AF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show between a d b; assumption)) (by (show between a e c; assumption)) (by (show b ≠ a; assumption)) (by (show a ≠ c; assumption)) (by (show f ≠ a; assumption)) (by (show ∠ d:a:f = ∠ e:a:f; assumption)))
  exact ⟨hfa, hangle⟩

end Elements.Book1
