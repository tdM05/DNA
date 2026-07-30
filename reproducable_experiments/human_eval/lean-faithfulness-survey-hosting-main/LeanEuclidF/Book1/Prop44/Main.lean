import SystemE
import Book1Variants.Prop29
import Book1.Prop31.Main
import Book1Variants.Prop42
import Book1.Prop43.Main
import Book1.Prop44.step1
import Book1.Prop44.step2
import Book1.Prop44.step3
import Book1.Prop44.step4
import Book1.Prop44.step5
import Book1.Prop44.step6
import Book1.Prop44.step7
import Book1.Prop44.step8
import Book1.Prop44.step9
import Book1.Prop44.step10
import Book1.Prop44.step11
import Book1.Prop44.step12
import Book1.Prop44.step13
import Book1.Prop44.step14
import Book1.Prop44.step15
import Book1.Prop44.step16
import Book1.Prop44.step17
import Book1.Prop44.step18
import Book1.Prop44.step19
import Book1.Prop44.step20
import Book1.Prop44.step6_assumption1
import Book1.Prop44.step20_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_44 : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) := by
  euclid_intros

  euclid_apply (proposition_42'' c₁ c₂ c₃ d₁ d₂ d₃ a b C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (f, g, e, GF, BG, EF)
  have s1 : formParallelogram f g b e GF AB BG EF ∧ ∠ e:b:f = ∠ d₁:d₂:d₃ ∧
      Triangle.area △ f:b:e + Triangle.area △ f:e:g = Triangle.area △ c₁:c₂:c₃ := by euclid_apply (h_1_44_s1 f g b e GF AB BG EF (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show f.onLine BG; assumption)) (by (show b.onLine BG; assumption)) (by (show g.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ∠ e:b:f = ∠ d₁:d₂:d₃; assumption)) (by (show (△f:b:e).area + (△f:e:g).area = (△c₁:c₂:c₃).area; assumption)))

  have s2 : between a b e := by euclid_apply (h_1_44_s2 a b e (by (show between a b e; assumption)))

  euclid_apply (proposition_31 a b f BG) as AH
  euclid_apply (intersection_lines AH GF) as h
  have s3 : between g f h := by euclid_apply (h_1_44_s3 a b e f g h AB BG EF GF AH (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show e.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show a ≠ b; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)))

  have s4 : h.onLine AH ∧ ¬(AH.intersectsLine BG) := by euclid_apply (h_1_44_s4 h AH BG (by (show h.onLine AH; assumption)) (by (show ¬(AH.intersectsLine BG); assumption)))

  euclid_apply (line_from_points h b) as HB
  have s5 : distinctPointsOnLine h b HB := by euclid_apply (h_1_44_s5 a b e f g h AB BG EF GF AH HB (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show e.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show a ≠ b; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)))

  have s6_a1 : ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF := by euclid_apply (h_1_44_s6_x1 a b e f g h AB BG EF GF AH (by (show h.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show a.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show e.onLine AB; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show a ≠ b; assumption)) (by (show between g f h; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)))

  have s6 : ∠ a:h:g + ∠ h:g:e = ∟ + ∟ := by euclid_apply (h_1_44_s6 a b e f g h AB BG EF GF AH HB (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show e.onLine AB; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show a ≠ b; assumption)) (by (show between g f h; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF; assumption)))

  have s7 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ := by euclid_apply (h_1_44_s7 a b d₁ d₂ d₃ e f g h AB BG EF GF AH (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show e.onLine AB; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show a ≠ b; assumption)) (by (show between g f h; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ∠ e:b:f = ∠ d₁:d₂:d₃; assumption)) (by (show (∠ d₁:d₂:d₃ : ℝ) > 0; assumption)) (by (show ∠ a:h:g + ∠ h:g:e = ∟ + ∟; assumption)))

  have s8 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF := by euclid_apply (h_1_44_s8 b e f g h BG EF GF AH HB (by (show f.onLine GF; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine GF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show b.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g ≠ e; assumption)) (by (show between g f h; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF; assumption)))

  have s9 : HB.intersectsLine EF := by euclid_apply (h_1_44_s9 b e f g h HB EF (by (show ∠ b:h:f + ∠ f:g:e < ∟ + ∟; assumption)) (by (show ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF; assumption)))

  euclid_apply (intersection_lines HB EF) as k
  have s10 : k.onLine HB ∧ k.onLine EF := by euclid_apply (h_1_44_s10 k HB EF (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)))

  euclid_apply (proposition_31 k a b AB) as KL
  have s11 : k.onLine KL ∧ ¬(KL.intersectsLine AB) := by euclid_apply (h_1_44_s11 k KL AB (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)))

  euclid_apply (intersection_lines KL AH) as l
  euclid_apply (intersection_lines KL BG) as m
  have s12 : between h a l ∧ between f b m := by euclid_apply (h_1_44_s12 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)))

  have s13 : formParallelogram h l g k AH EF GF KL := by euclid_apply (h_1_44_s13 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)) (by (show between g f h; assumption)) (by (show GF.intersectsLine AH; assumption)) (by (show between h a l ∧ between f b m; assumption)))

  have s14 : b.onLine HB ∧ between h b k := by euclid_apply (h_1_44_s14 a b e f g h k AB BG EF GF AH HB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show h ≠ b; assumption)))

  have s15 : formParallelogram h a f b AH BG GF AB ∧ formParallelogram b m e k BG EF AB KL := by euclid_apply (h_1_44_s15 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)) (by (show between h a l ∧ between f b m; assumption)) (by (show formParallelogram h l g k AH EF GF KL; assumption)))

  have s16 : formParallelogram b m a l BG AH AB KL ∧ formParallelogram f g b e GF AB BG EF := by euclid_apply (h_1_44_s16 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)) (by (show h ≠ b; assumption)) (by (show between h a l ∧ between f b m; assumption)) (by (show formParallelogram h l g k AH EF GF KL; assumption)) (by (show b.onLine HB ∧ between h b k; assumption)) (by (show formParallelogram h a f b AH BG GF AB ∧ formParallelogram b m e k BG EF AB KL; assumption)))

  have s17 : Triangle.area △ a:b:m + Triangle.area △ a:l:m =
      Triangle.area △ f:g:e + Triangle.area △ f:e:b := by euclid_apply (h_1_44_s17 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show between h a l ∧ between f b m; assumption)) (by (show formParallelogram h l g k AH EF GF KL; assumption)) (by (show b.onLine HB ∧ between h b k; assumption)) (by (show formParallelogram h a f b AH BG GF AB ∧ formParallelogram b m e k BG EF AB KL; assumption)))

  have s18 : Triangle.area △ f:g:e + Triangle.area △ f:e:b = Triangle.area △ c₁:c₂:c₃ := by euclid_apply (h_1_44_s18 b e f g c₁ c₂ c₃ (by (show Triangle.area △ f:b:e + Triangle.area △ f:e:g = Triangle.area △ c₁:c₂:c₃; assumption)))

  have s19 : Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃ := by euclid_apply (h_1_44_s19 a b l m c₁ c₂ c₃ f e g (by (show Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ f:g:e + Triangle.area △ f:e:b; assumption)) (by (show Triangle.area △ f:g:e + Triangle.area △ f:e:b = Triangle.area △ c₁:c₂:c₃; assumption)))

  have s20_a1 : ∠ e:b:f = ∠ a:b:m := by euclid_apply (h_1_44_s20_x1 a b e f h l m AB AH BG EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show m.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show between a b e; assumption)) (by (show between h a l ∧ between f b m; assumption)))

  have s20_a2 : ∠ e:b:f = ∠ d₁:d₂:d₃ := by assumption

  have s20 : ∠ a:b:m = ∠ d₁:d₂:d₃ := by euclid_apply (h_1_44_s20 a b e f h l m d₁ d₂ d₃ AB AH BG EF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show m.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show between a b e; assumption)) (by (show between h a l ∧ between f b m; assumption)) (by (show ∠ e:b:f = ∠ a:b:m; assumption)) (by (show ∠ e:b:f = ∠ d₁:d₂:d₃; assumption)))

  exact ⟨m, l, BG, AH, KL, s16.1, s20, s19⟩

end Elements.Book1
