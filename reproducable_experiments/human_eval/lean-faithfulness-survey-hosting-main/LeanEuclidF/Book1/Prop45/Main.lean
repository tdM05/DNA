import SystemE
import Book1Variants.Prop42
import Book1Variants.Prop44
import Book1.Prop45.step1
import Book1.Prop45.step2
import Book1.Prop45.step3
import Book1.Prop45.step4
import Book1.Prop45.step5
import Book1.Prop45.step6
import Book1.Prop45.step7
import Book1.Prop45.step8
import Book1.Prop45.step9
import Book1.Prop45.step10
import Book1.Prop45.step11
import Book1.Prop45.step12
import Book1.Prop45.step13
import Book1.Prop45.step14
import Book1.Prop45.step15
import Book1.Prop45.step16
import Book1.Prop45.step17
import Book1.Prop45.step18
import Book1.Prop45.step19
import Book1.Prop45.step20
import Book1.Prop45.step21
import Book1.Prop45.step17_assumption1
import Book1.Prop45.step17_assumption2
import Book1.Prop45.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by
  euclid_intros

  have s1 : distinctPointsOnLine d b DB := by euclid_apply (h_1_45_s1 a b d AB DB AD (by (show b.onLine DB; assumption)) (by (show d.onLine DB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show AD ≠ AB; assumption)) (by (show a ≠ b; assumption)))

  euclid_apply (proposition_42 a b d e₁ e₂ e₃ AB DB AD E₁₂ E₂₃) as (f, g, k, h, FG, KH, FK, GH)
  have s2 : formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) := by euclid_apply (h_1_45_s2 f g k h FG KH FK GH e₁ e₂ e₃ a b d (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show f.onLine FK; assumption)) (by (show k.onLine FK; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show f.sameSide k GH; assumption)) (by (show g ≠ h; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show ¬FK.intersectsLine GH; assumption)) (by (show ∠h:k:f = ∠e₁:e₂:e₃; assumption)) (by (show Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d; assumption)))

  euclid_apply (proposition_44' g h d b c e₁ e₂ e₃ k GH DB BC CD E₁₂ E₂₃) as (m, l, HM, GL, LM)
  have s3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) := by euclid_apply (h_1_45_s3 h m g l HM GL GH LM e₁ e₂ e₃ d b c (by (show h.onLine HM; assumption)) (by (show m.onLine HM; assumption)) (by (show g.onLine GL; assumption)) (by (show l.onLine GL; assumption)) (by (show h.onLine GH; assumption)) (by (show g.onLine GH; assumption)) (by (show m.onLine LM; assumption)) (by (show l.onLine LM; assumption)) (by (show h.sameSide g LM; assumption)) (by (show m ≠ l; assumption)) (by (show ¬HM.intersectsLine GL; assumption)) (by (show ¬GH.intersectsLine LM; assumption)) (by (show ∠g:h:m = ∠e₁:e₂:e₃; assumption)) (by (show Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c; assumption)))

  have s4_a1 : ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m := by euclid_finish

  have s4 : ∠ h:k:f = ∠ g:h:m := by euclid_apply (h_1_45_s4 e₁ e₂ e₃ h k f g m (by (show ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m; assumption)))

  have s5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g := by euclid_apply (h_1_45_s5 h k f g m (by (show ∠ h:k:f = ∠ g:h:m; assumption)))

  have s6 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by euclid_apply (h_1_45_s6 f k h g m FG KH GH (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show f.sameSide k GH; assumption)) (by (show g ≠ h; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g; assumption)))

  have s7 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by euclid_apply (h_1_45_s7 f g k h FK GH KH FG (by (show f.onLine FK; assumption)) (by (show k.onLine FK; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show ¬k.onLine GH; assumption)) (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show f.sameSide k GH; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show ¬FK.intersectsLine GH; assumption)))

  have s8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by euclid_apply (h_1_45_s8 f g k h m (by (show ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m; assumption)) (by (show ∠ f:k:h + ∠ k:h:g = ∟ + ∟; assumption)))

  have s9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by euclid_apply (h_1_45_s9 k m g h GH (by (show ¬k.onLine GH; assumption)) (by (show ¬m.onLine GH; assumption)) (by (show ¬m.sameSide k GH; assumption)) (by (show ∠ k:h:g + ∠ g:h:m = ∟ + ∟; assumption)))

  have s10 : KH = HM := by euclid_apply (h_1_45_s10 g k h m GH KH HM (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show m.onLine HM; assumption)) (by (show h.onLine HM; assumption)) (by (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)))

  have s11_a1 : ¬(FG.intersectsLine KH) := by assumption

  have s11 : ∠ m:h:g = ∠ h:g:f := by euclid_apply (h_1_45_s11 f g k h m FG GH KH HM (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show h.onLine HM; assumption)) (by (show m.onLine HM; assumption)) (by (show f.sameSide k GH; assumption)) (by (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by (show KH = HM; assumption)) (by (show ¬(FG.intersectsLine KH); assumption)))

  have s12 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by euclid_apply (h_1_45_s12 f g h m l (by (show ∠ m:h:g = ∠ h:g:f; assumption)))

  have s13 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l := by euclid_apply (h_1_45_s13 f g h m l (by (show ∠ m:h:g = ∠ h:g:f; assumption)))

  have s14 : ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by euclid_apply (h_1_45_s14 g h m l GL HM GH LM (by (show g.onLine GL; assumption)) (by (show l.onLine GL; assumption)) (by (show h.onLine HM; assumption)) (by (show m.onLine HM; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show l.onLine LM; assumption)) (by (show m.onLine LM; assumption)) (by (show ¬m.onLine GH; assumption)) (by (show h.sameSide g LM; assumption)) (by (show ¬HM.intersectsLine GL; assumption)) (by (show ¬GH.intersectsLine LM; assumption)))

  have s15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟ := by euclid_apply (h_1_45_s15 f g h m l (by (show ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l; assumption)) (by (show ∠ m:h:g + ∠ h:g:l = ∟ + ∟; assumption)))

  have s16 : FG = GL := by euclid_apply (h_1_45_s16 f g h k m l FG GL GH LM (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show g.onLine GL; assumption)) (by (show l.onLine GL; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show f.sameSide k GH; assumption)) (by (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by (show l.onLine LM; assumption)) (by (show m.onLine LM; assumption)) (by (show h.sameSide g LM; assumption)) (by (show ¬GH.intersectsLine LM; assumption)) (by (show ∠ h:g:f + ∠ h:g:l = ∟ + ∟; assumption)))

  have s17_a1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH) := by euclid_apply (h_1_45_s17_x1 f g k h FG KH FK GH (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show f.onLine FK; assumption)) (by (show k.onLine FK; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show f.sameSide k GH; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show ¬FK.intersectsLine GH; assumption)))

  have s17_a2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by euclid_apply (h_1_45_s17_x2 h m g l HM GL GH LM (by (show h.onLine HM; assumption)) (by (show m.onLine HM; assumption)) (by (show g.onLine GL; assumption)) (by (show l.onLine GL; assumption)) (by (show h.onLine GH; assumption)) (by (show g.onLine GH; assumption)) (by (show m.onLine LM; assumption)) (by (show l.onLine LM; assumption)) (by (show m ≠ l; assumption)) (by (show h.sameSide g LM; assumption)) (by (show ¬HM.intersectsLine GL; assumption)) (by (show ¬GH.intersectsLine LM; assumption)))

  have s17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by euclid_apply (h_1_45_s17 f g k h m l FK FG GL GH LM KH (by (show f.onLine FK; assumption)) (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show l.onLine GL; assumption)) (by (show g.onLine GH; assumption)) (by (show m.onLine LM; assumption)) (by (show l.onLine LM; assumption)) (by (show ¬m.onLine GH; assumption)) (by (show f.sameSide k GH; assumption)) (by (show h.sameSide g LM; assumption)) (by (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by (show FG = GL; assumption)) (by (show |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH); assumption)) (by (show |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM); assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show k.onLine FK; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show ¬FG.intersectsLine KH; assumption)))

  have s18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by euclid_apply (h_1_45_s18 f g k h m l FG GL GH KH HM LM (by (show k.onLine KH; assumption)) (by (show m.onLine HM; assumption)) (by (show f.onLine FG; assumption)) (by (show l.onLine GL; assumption)) (by (show l.onLine LM; assumption)) (by (show m.onLine LM; assumption)) (by (show f.sameSide k GH; assumption)) (by (show h.sameSide g LM; assumption)) (by (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by (show KH = HM; assumption)) (by (show FG = GL; assumption)) (by (show ¬GH.intersectsLine LM; assumption)))

  have s19 : |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by euclid_apply (h_1_45_s19 f g k h m l FK FG GL GH KH LM (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show k.onLine FK; assumption)) (by (show f.onLine FK; assumption)) (by (show g ≠ h; assumption)) (by (show f.sameSide k GH; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM; assumption)) (by (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)) (by (show m.onLine LM; assumption)) (by (show l.onLine LM; assumption)) (by (show m ≠ l; assumption)))

  have s20 : formParallelogram f l k m FG KH FK LM := by euclid_apply (h_1_45_s20 f g k h m l FG GL GH KH HM FK LM (by (show f.onLine FG; assumption)) (by (show g.onLine FG; assumption)) (by (show k.onLine KH; assumption)) (by (show m.onLine HM; assumption)) (by (show f.onLine FK; assumption)) (by (show k.onLine FK; assumption)) (by (show l.onLine GL; assumption)) (by (show l.onLine LM; assumption)) (by (show m.onLine LM; assumption)) (by (show m ≠ l; assumption)) (by (show h.sameSide g LM; assumption)) (by (show KH = HM; assumption)) (by (show ¬FG.intersectsLine KH; assumption)) (by (show FG = GL; assumption)) (by (show |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM; assumption)) (by (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)))

  have s21_a1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d := by assumption

  have s21_a2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c := by assumption

  have s21 : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by euclid_apply (h_1_45_s21 a b c d f g k h m l FG KH FK GH LM (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show g.onLine GH; assumption)) (by (show h.onLine GH; assumption)) (by (show g.onLine FG; assumption)) (by (show m.onLine LM; assumption)) (by (show l.onLine LM; assumption)) (by (show f.sameSide k GH; assumption)) (by (show h.sameSide g LM; assumption)) (by (show k.opposingSides m GH ∧ ∠k:h:g + ∠g:h:m = ∟ + ∟; assumption)) (by (show |(h─g)| = |(m─l)| ∧ ¬GH.intersectsLine LM; assumption)) (by (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)) (by (show formParallelogram f l k m FG KH FK LM; assumption)) (by (show Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d; assumption)) (by (show Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c; assumption)))

  use f, l, k, m, FG, KH, FK, LM
  have hangle : ∠ f:k:m = ∠ e₁:e₂:e₃ := by euclid_apply (h_1_45_x1 e₁ e₂ e₃ f g k h m l FG KH FK GH (by (show k.onLine KH; assumption)) (by (show h.onLine KH; assumption)) (by (show k.onLine FK; assumption)) (by (show f.onLine FK; assumption)) (by (show h.onLine GH; assumption)) (by (show g ≠ h; assumption)) (by (show ∠ h:k:f = ∠ e₁:e₂:e₃; assumption)) (by (show k.opposingSides m GH ∧ ∠ k:h:g + ∠ g:h:m = ∟ + ∟; assumption)) (by (show |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH; assumption)) (by (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)))
  exact ⟨s20, hangle, s21⟩

end Elements.Book1
