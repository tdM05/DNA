import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Book1.Prop06.step1
import Book1.Prop06.step2
import Book1.Prop06.step3
import Book1.Prop06.step4
import Book1.Prop06.step5
import Book1.Prop06.step6
import Book1.Prop06.step7
import Book1.Prop06.step8
import Book1.Prop06.step9
import Book1.Prop06.step10
import Book1.Prop06.step11
import Book1.Prop06.swapfig
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| := by
  euclid_intros

  have habsurd : ¬ (|(a─b)| ≠ |(a─c)|) := by
    intro hne

    have s1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by euclid_apply (h_1_6_s1 a b c (by (show |(a─b)| ≠ |(a─c)|; assumption)))

    wlog hgt : |(a─b)| > |(a─c)| generalizing b c AB BC AC with Hsym

    · have swapfig :
          (∠ a:c:b = ∠ a:b:c)
          ∧ (a ≠ c)
          ∧ (AC ≠ BC)
          ∧ (BC ≠ AB)
          ∧ (AB ≠ AC)
          ∧ (|(a─c)| ≠ |(a─b)|)
          ∧ (|(a─c)| > |(a─b)| ∨ |(a─b)| > |(a─c)|)
          ∧ (|(a─c)| > |(a─b)|) := by euclid_apply (h_1_6_x1 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ∠ a:b:c = ∠ a:c:b; assumption)) (by (show |(a─b)| ≠ |(a─c)|; assumption)) (by (show |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|; assumption)) (by (show ¬ |(a─b)| > |(a─c)|; assumption)))
      obtain ⟨hang', hac, hACBC, hBCAB, hABAC, hne', hor', hgt'⟩ := swapfig
      exact Hsym c b AC BC AB hang' (by assumption) (by assumption) hac (by assumption)
        (by assumption) (by assumption) (by assumption) hACBC hBCAB hABAC hne' hor' hgt'

    · have s2 : |(a─b)| > |(a─c)| := by euclid_apply (h_1_6_s2 a b c (by (show |(a─b)| > |(a─c)|; assumption)))
      euclid_apply (proposition_3 b a a c AB AC) as d
      have s3 : between b d a ∧ |(b─d)| = |(a─c)| := by euclid_apply (h_1_6_s3 a b c d (by (show between b d a; assumption)) (by (show |(b─d)| = |(a─c)|; assumption)))
      euclid_apply (line_from_points d c) as DC
      have s4 : d.onLine DC ∧ c.onLine DC := by euclid_apply (h_1_6_s4 d c DC (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)))
      have s5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by euclid_apply (h_1_6_s5 a b c d (by (show |(b─d)| = |(a─c)|; assumption)))
      have s6 : ∠ d:b:c = ∠ a:c:b := by euclid_apply (h_1_6_s6 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b d a; assumption)) (by (show ∠ a:b:c = ∠ a:c:b; assumption)))
      have s7 : |(d─c)| = |(a─b)| := by euclid_apply (h_1_6_s7 a b c d AB BC AC DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b d a; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show |(b─d)| = |(a─c)|; assumption)) (by (show ∠ d:b:c = ∠ a:c:b; assumption)))
      have s8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by euclid_apply (h_1_6_s8 a b c d AB BC AC DC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b d a; assumption)) (by (show d.onLine DC; assumption)) (by (show c.onLine DC; assumption)) (by (show |(b─d)| = |(a─c)|; assumption)) (by (show ∠ d:b:c = ∠ a:c:b; assumption)))
      have s9 : False := by euclid_apply (h_1_6_s9 a b c d AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b d a; assumption)) (by (show |(b─d)| = |(a─c)|; assumption)) (by (show ∠ d:b:c = ∠ a:c:b; assumption)) (by (show |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a); assumption)))
      exact s9
  have s10 : ¬ (|(a─b)| ≠ |(a─c)|) := by euclid_apply (h_1_6_s10 a b c (by (show ¬ (|(a─b)| ≠ |(a─c)|); assumption)))
  have s11 : |(a─b)| = |(a─c)| := by euclid_apply (h_1_6_s11 a b c (by (show ¬ (|(a─b)| ≠ |(a─c)|); assumption)))
  exact s11

end Elements.Book1
