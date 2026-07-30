import SystemE
import Book1Variants.Prop11
import Book1.Prop03.Main
import Book1.Prop31.Main
import Book1.Prop46.step1
import Book1.Prop46.step2
import Book1.Prop46.step3
import Book1.Prop46.step4
import Book1.Prop46.step5
import Book1.Prop46.step6
import Book1.Prop46.step7
import Book1.Prop46.step8
import Book1.Prop46.step9
import Book1.Prop46.step10
import Book1.Prop46.step12
import Book1.Prop46.step13
import Book1.Prop46.step14
import Book1.Prop46.step15
import Book1.Prop46.step16
import Book1.Prop46.step17
import Book1.Prop46.step18
import Book1.Prop46.step19
import Book1.Prop46.hbe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  euclid_intros

  euclid_apply (extend_point AB b a) as g
  euclid_apply (proposition_11 b g a AB) as c
  euclid_apply (line_from_points a c) as AC
  have s1 : ∠ c:a:b = ∟ := by euclid_apply (h_1_46_s1 a b c AB (by (show ∠ b:a:c = ∟; assumption)) (by (show a.onLine AB; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show a ≠ b; assumption)))

  euclid_apply (extend_point_longer AC a c (a─b)) as c1
  euclid_apply (proposition_3 a c1 a b AC AB) as d
  euclid_apply (line_from_points a d) as AD
  have s2 : |(a─d)| = |(a─b)| := by euclid_apply (h_1_46_s2 a b d (by (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (proposition_31 d a b AB) as DE
  have s3 : d.onLine DE ∧ ¬(DE.intersectsLine AB) := by euclid_apply (h_1_46_s3 a b d AB DE (by (show d.onLine DE; assumption)) (by (show ¬(DE.intersectsLine AB); assumption)))

  euclid_apply (proposition_31 b a d AD) as BE
  euclid_apply (intersection_lines DE BE) as e
  have s4 : b.onLine BE ∧ ¬(BE.intersectsLine AD) := by euclid_apply (h_1_46_s4 a b d AD BE (by (show b.onLine BE; assumption)) (by (show ¬(BE.intersectsLine AD); assumption)))

  have s5 : formParallelogram d e a b DE AB AD BE := by euclid_apply (h_1_46_s5 a b c d e c1 AB AC AD BE DE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show c1.onLine AC; assumption)) (by (show between a d c1; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show ¬DE.intersectsLine AB; assumption)) (by (show ¬BE.intersectsLine AD; assumption)) (by (show |(a─d)| = |(a─b)|; assumption)))

  have s6 : |(a─b)| = |(d─e)| := by euclid_apply (h_1_46_s6 a b d e AB AD BE DE (by (show formParallelogram d e a b DE AB AD BE; assumption)))

  have s7 : |(a─d)| = |(b─e)| := by euclid_apply (h_1_46_s7 a b d e AB AD BE DE (by (show formParallelogram d e a b DE AB AD BE; assumption)))

  have s8 : |(a─b)| = |(a─d)| := by euclid_apply (h_1_46_s8 a b d (by (show |(a─d)| = |(a─b)|; assumption)))

  have s9 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| := by euclid_apply (h_1_46_s9 a b d e (by (show |(a─d)| = |(a─b)|; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─d)| = |(b─e)|; assumption)))

  have s10 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| := by euclid_apply (h_1_46_s10 a b d e (by (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  have s12_a1 : ¬(DE.intersectsLine AB) := by assumption

  have s12 : ∠ b:a:d + ∠ a:d:e = ∟ + ∟ := by euclid_apply (h_1_46_s12 a b c d e c1 AB AC AD BE DE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c1.onLine AC; assumption)) (by (show between a d c1; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show ¬(DE.intersectsLine AB); assumption)) (by (show ¬(BE.intersectsLine AD); assumption)) (by (show |(a─b)| = |(d─e)|; assumption)))

  have s13 : ∠ b:a:d = ∟ := by euclid_apply (h_1_46_s13 a b c d c1 AB AC AD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c1.onLine AC; assumption)) (by (show between a c c1; assumption)) (by (show between a d c1; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show ∠ c:a:b = ∟; assumption)))

  have s14 : ∠ a:d:e = ∟ := by euclid_apply (h_1_46_s14 a b d e (by (show ∠ b:a:d + ∠ a:d:e = ∟ + ∟; assumption)) (by (show ∠ b:a:d = ∟; assumption)))

  have s15 : formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e) := by euclid_apply (h_1_46_s15 a b d e AB AD BE DE)

  have s16 : ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ := by euclid_apply (h_1_46_s16 a b d e AB AD BE DE (by (show formParallelogram d e a b DE AB AD BE; assumption)) (by (show ∠ b:a:d = ∟; assumption)) (by (show ∠ a:d:e = ∟; assumption)) (by (show formParallelogram d e a b DE AB AD BE → (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e); assumption)))

  have s17 : ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ := by euclid_apply (h_1_46_s17 a b d e (by (show ∠ b:a:d = ∟; assumption)) (by (show ∠ a:d:e = ∟; assumption)) (by (show ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟; assumption)))

  have s18 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| := by euclid_apply (h_1_46_s18 a b d e (by (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  have s19 : (|(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) ∧
      (∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) := by euclid_apply (h_1_46_s19 a b d e (by (show ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟; assumption)) (by (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  have hbe : |(b─e)| = |(a─b)| := by euclid_apply (h_1_46_x1 a b d e (by (show |(a─d)| = |(a─b)|; assumption)) (by (show |(a─d)| = |(b─e)|; assumption)))
  exact ⟨d, e, DE, AD, BE, s5, s6.symm, s2, hbe, s13, s14, s16.1, s16.2⟩

end Elements.Book1
