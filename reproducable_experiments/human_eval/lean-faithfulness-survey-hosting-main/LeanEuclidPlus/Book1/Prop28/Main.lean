import SystemE
import Book1.Prop28.step1
import Book1.Prop28.step2
import Book1.Prop28.step3
import Book1.Prop28.step4
import Book1.Prop28.step5
import Book1.Prop28.step6
import Book1.Prop28.step7
import Book1.Prop28.step8
import Book1.Prop28.step1_assumption2
import Book1.Prop28.step4_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_28 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) := by
  euclid_intros

  have h_or : ∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by assumption
  rcases h_or with h1 | h2
  ·

    have s1_a1 : ∠ e:g:b = ∠ g:h:d := by assumption

    have s1_a2 : ∠ e:g:b = ∠ a:g:h := by euclid_apply (h_1_28_s1_x1 a b d e f g h AB EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))

    have s1 : ∠ a:g:h = ∠ g:h:d := by euclid_apply (h_1_28_s1 a b d e f g h AB EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)) (by (show ∠ e:g:b = ∠ g:h:d; assumption)) (by (show ∠ e:g:b = ∠ a:g:h; assumption)))
    have s2 : a.opposingSides d EF := by euclid_apply (h_1_28_s2 a b d e f g h EF (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))
    have s3 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_28_s3 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show ∠ a:g:h = ∠ g:h:d; assumption)) (by (show a.opposingSides d EF; assumption)))
    exact s3 (by assumption)
  ·

    have s4_a1 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by assumption

    have s4_a2 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟ := by euclid_apply (h_1_28_s4_x1 a b d e f g h AB EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))

    have s4 : ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := by euclid_apply (h_1_28_s4 a b d e f g h AB EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)) (by (show ∠ b:g:h + ∠ g:h:d = ∟ + ∟; assumption)) (by (show ∠ a:g:h + ∠ b:g:h = ∟ + ∟; assumption)))
    have s5 : ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h := by euclid_apply (h_1_28_s5 (by (show ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)))
    have s6 : ∠ a:g:h = ∠ g:h:d := by euclid_apply (h_1_28_s6 (by (show ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h; assumption)))
    have s7 : a.opposingSides d EF := by euclid_apply (h_1_28_s7 a b d e f g h EF (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show between a g b; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show b.sameSide d EF; assumption)))
    have s8 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_28_s8 a b c d e f g h AB CD EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show between a g b; assumption)) (by (show between c h d; assumption)) (by (show between e g h; assumption)) (by (show between g h f; assumption)) (by (show ∠ a:g:h = ∠ g:h:d; assumption)) (by (show a.opposingSides d EF; assumption)))
    exact s8 (by assumption)

end Elements.Book1
