import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop11
import Book1.Prop48.step1
import Book1.Prop48.step2
import Book1.Prop48.step3
import Book1.Prop48.step4
import Book1.Prop48.step5
import Book1.Prop48.step6
import Book1.Prop48.step7
import Book1.Prop48.step8
import Book1.Prop48.step9
import Book1.Prop48.step10
import Book1.Prop48.step11
import Book1.Prop48.step12
import Book1.Prop48.step13
import Book1.Prop48.step14
import Book1.Prop48.step15
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ := by
  euclid_intros

  euclid_apply (proposition_11'' a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  have s1 : ∠ d:a:c = ∟ := by euclid_apply (h_1_48_s1 a b c d d' d'' d''' AB BC AC AD (by (show ¬d'.onLine AC; assumption)) (by (show ∠d':a:c = ∟; assumption)) (by (show a.onLine AD; assumption)) (by (show d'.onLine AD; assumption)) (by (show d''.onLine AD; assumption)) (by (show between d' a d''; assumption)) (by (show d'''.onLine AD; assumption)) (by (show between d'' a d'''; assumption)) (by (show between a d d'''; assumption)) (by (show |(a─d)| = |(a─b)|; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)))

  have s2 : |(a─d)| = |(b─a)| := by euclid_apply (h_1_48_s2 (by (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (line_from_points d c) as DC
  have s3 : distinctPointsOnLine d c DC := by euclid_apply (h_1_48_s3 a b c d d' d'' d''' AC AD DC (by (show ¬d'.onLine AC; assumption)) (by (show a.onLine AD; assumption)) (by (show d'.onLine AD; assumption)) (by (show d'''.onLine AD; assumption)) (by (show between a d d'''; assumption)) (by (show |(a─d)| = |(a─b)|; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)))

  have s4_a1 : |(d─a)| = |(a─b)| := by euclid_finish

  have s4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)| := by euclid_apply (h_1_48_s4 (by (show |(d─a)| = |(a─b)|; assumption)))

  have s5 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)| := by euclid_apply (h_1_48_s5 (by (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)))

  have s6 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by euclid_apply (h_1_48_s6 (by (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)))

  have s7_a1 : ∠ d:a:c = ∟ := by assumption

  have s7 : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| := by euclid_apply (h_1_48_s7 a b c d d' d'' d''' AB BC AC AD DC (by (show ¬d'.onLine AC; assumption)) (by (show ∠d':a:c = ∟; assumption)) (by (show a.onLine AD; assumption)) (by (show d'.onLine AD; assumption)) (by (show d''.onLine AD; assumption)) (by (show between d' a d''; assumption)) (by (show d'''.onLine AD; assumption)) (by (show between d'' a d'''; assumption)) (by (show |(a─d''')| > |(a─b)|; assumption)) (by (show between a d d'''; assumption)) (by (show |(a─d)| = |(a─b)|; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show ∠ d:a:c = ∟; assumption)))

  have s8_a1 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by assumption

  have s8 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by euclid_apply (h_1_48_s8 (by (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  have s9 : |(d─c)| * |(d─c)| = |(b─c)| * |(b─c)| := by euclid_apply (h_1_48_s9 (by (show |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)) (by (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  have s10 : |(d─c)| = |(b─c)| := by euclid_apply (h_1_48_s10 (by (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)) (by (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  have s11_a1 : |(d─a)| = |(a─b)| := by assumption

  have s11_a2 : distinctPointsOnLine a c AC := by euclid_finish

  have s11 : |(d─a)| = |(b─a)| ∧ |(a─c)| = |(a─c)| := by euclid_apply (h_1_48_s11 (by (show |(d─a)| = |(a─b)|; assumption)) (by (show distinctPointsOnLine a c AC; assumption)))

  have s12 : |(d─c)| = |(b─c)| := by euclid_apply (h_1_48_s12 (by (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)) (by (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  have s13 : ∠ d:a:c = ∠ b:a:c := by euclid_apply (h_1_48_s13 a b c d d' d'' d''' AB BC AC AD DC (by (show ¬d'.onLine AC; assumption)) (by (show a.onLine AD; assumption)) (by (show d'.onLine AD; assumption)) (by (show d''.onLine AD; assumption)) (by (show between d' a d''; assumption)) (by (show d'''.onLine AD; assumption)) (by (show between d'' a d'''; assumption)) (by (show between a d d'''; assumption)) (by (show |(a─d)| = |(a─b)|; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show |(d─c)| = |(b─c)|; assumption)))

  have s14 : ∠ d:a:c = ∟ := by euclid_apply (h_1_48_s14 (by (show ∠ d:a:c = ∟; assumption)))

  have s15 : ∠ b:a:c = ∟ := by euclid_apply (h_1_48_s15 (by (show ∠ d:a:c = ∠ b:a:c; assumption)) (by (show ∠ d:a:c = ∟; assumption)))

  exact s15

end Elements.Book1
