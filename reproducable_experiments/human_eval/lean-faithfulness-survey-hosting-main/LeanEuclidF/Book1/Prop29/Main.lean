import SystemE
import Book1.Prop13.Main
import Book1.Prop15.Main
import Book1.Prop29.step1
import Book1.Prop29.step2
import Book1.Prop29.step3
import Book1.Prop29.step4
import Book1.Prop29.step5
import Book1.Prop29.step6
import Book1.Prop29.step7
import Book1.Prop29.step8
import Book1.Prop29.step9
import Book1.Prop29.step10
import Book1.Prop29.step11
import Book1.Prop29.step12
import Book1.Prop29.step13
import Book1.Prop29.step14
import Book1.Prop29.step15
import Book1.Prop29.step16
import Book1.Prop29.step17
import Book1.Prop29.hreduction
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_29 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by
  euclid_intros

  have habsurd : ¬(∠ a:g:h ≠ ∠ g:h:d) := by
    intro hne

    have s1_a1 : ∠ a:g:h ≠ ∠ g:h:d := by assumption

    have s1 : ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h := by euclid_apply (h_1_29_s1 (by (show ∠ a:g:h ≠ ∠ g:h:d; assumption)))

    wlog hgt : ∠ a:g:h > ∠ g:h:d generalizing a b c d g h AB CD with Hsym

    · have hreduction : False := by euclid_apply (h_1_29_x1 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show ∠ a:g:h ≠ ∠ g:h:d; assumption)) (by (show ¬∠ a:g:h > ∠ g:h:d; assumption)) (by (show ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h; assumption)))
      exact hreduction

    ·
      have s2 : ∠ a:g:h > ∠ g:h:d := by euclid_apply (h_1_29_s2 (by (show ∠ a:g:h > ∠ g:h:d; assumption)))
      have s3 : ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h := by euclid_apply (h_1_29_s3 )
      have s4 : ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d := by euclid_apply (h_1_29_s4 (by (show ∠ a:g:h > ∠ g:h:d; assumption)) (by (show ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h; assumption)))
      have s5 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟ := by euclid_apply (h_1_29_s5 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))
      have s6 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟ := by euclid_apply (h_1_29_s6 (by (show ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d; assumption)) (by (show ∠ a:g:h + ∠ b:g:h = ∟ + ∟; assumption)))
      have s7 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD := by euclid_apply (h_1_29_s7 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)) (by (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟; assumption)))
      have s8 : AB.intersectsLine CD := by euclid_apply (h_1_29_s8 AB CD (by (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟; assumption)) (by (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD; assumption)))

      have s9_a1 : ¬(AB.intersectsLine CD) := by assumption

      have s9 : False := by euclid_apply (h_1_29_s9 AB CD (by (show AB.intersectsLine CD; assumption)) (by (show ¬(AB.intersectsLine CD); assumption)))
      exact s9
  have s10 : ¬(∠ a:g:h ≠ ∠ g:h:d) := by euclid_apply (h_1_29_s10 (by (show ¬(∠ a:g:h ≠ ∠ g:h:d); assumption)))
  have s11 : ∠ a:g:h = ∠ g:h:d := by euclid_apply (h_1_29_s11 (by (show ¬(∠ a:g:h ≠ ∠ g:h:d); assumption)))
  have s12 : ∠ a:g:h = ∠ e:g:b := by euclid_apply (h_1_29_s12 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))
  have s13 : ∠ e:g:b = ∠ g:h:d := by euclid_apply (h_1_29_s13 (by (show ∠ a:g:h = ∠ g:h:d; assumption)) (by (show ∠ a:g:h = ∠ e:g:b; assumption)))
  have s14 : ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := by euclid_apply (h_1_29_s14 )
  have s15 : ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := by euclid_apply (h_1_29_s15 (by (show ∠ e:g:b = ∠ g:h:d; assumption)) (by (show ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)))
  have s16 : ∠ e:g:b + ∠ b:g:h = ∟ + ∟ := by euclid_apply (h_1_29_s16 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))
  have s17 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by euclid_apply (h_1_29_s17 (by (show ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)) (by (show ∠ e:g:b + ∠ b:g:h = ∟ + ∟; assumption)))
  exact ⟨s11, s13, s17⟩

end Elements.Book1
