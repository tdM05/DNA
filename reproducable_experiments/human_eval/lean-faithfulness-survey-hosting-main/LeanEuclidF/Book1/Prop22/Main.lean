import SystemE
import Book1.Prop03.Main
import Book1.Prop22.step1
import Book1.Prop22.step2
import Book1.Prop22.step3
import Book1.Prop22.step4
import Book1.Prop22.step5
import Book1.Prop22.step6
import Book1.Prop22.step7
import Book1.Prop22.step9
import Book1.Prop22.step10
import Book1.Prop22.step11
import Book1.Prop22.step12
import Book1.Prop22.step13
import Book1.Prop22.step14
import Book1.Prop22.step15
import Book1.Prop22.step16
import Book1.Prop22.hcut
import Book1.Prop22.hgoal1
import Book1.Prop22.hgoal2
import Book1.Prop22.hgoal3
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_22 : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) := by
  euclid_intros

  euclid_apply arbitrary_point as d
  euclid_apply (distinct_points d) as e'
  euclid_apply (line_from_points d e') as DE
  euclid_apply (extend_point_longer DE d e' (a─a')) as e''
  euclid_apply (extend_point_longer DE d e'' (b─b')) as e'''
  euclid_apply (extend_point_longer DE d e''' (c─c')) as e
  have s1 : distinctPointsOnLine d e DE := by euclid_apply (h_1_22_s1 d e DE (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show between d e''' e; assumption)))

  euclid_apply (proposition_3 d e a a' DE A) as f
  have s2 : |(d─f)| = |(a─a')| := by euclid_apply (h_1_22_s2 d f a a' (by (show |(d─f)| = |(a─a')|; assumption)))

  euclid_apply (proposition_3 f e b b' DE B) as g
  have s3 : |(f─g)| = |(b─b')| := by euclid_apply (h_1_22_s3 f g b b' (by (show |(f─g)| = |(b─b')|; assumption)))

  euclid_apply (proposition_3 g e c c' DE C) as h
  have s4 : |(g─h)| = |(c─c')| := by euclid_apply (h_1_22_s4 g h c c' (by (show |(g─h)| = |(c─c')|; assumption)))

  euclid_apply (circle_from_points f d) as DKL
  have s5 : f.isCentre DKL ∧ d.onCircle DKL := by euclid_apply (h_1_22_s5 f d DKL (by (show f.isCentre DKL; assumption)) (by (show d.onCircle DKL; assumption)))

  euclid_apply (circle_from_points g h) as KLH
  have s6 : g.isCentre KLH ∧ h.onCircle KLH := by euclid_apply (h_1_22_s6 g h KLH (by (show g.isCentre KLH; assumption)) (by (show h.onCircle KLH; assumption)))

  euclid_apply (intersection_circle_line_extending_points KLH DE g h) as i
  have hcut : KLH.intersectsCircle DKL := by euclid_apply (h_1_22_x1 d e f g h i DE DKL KLH a a' b b' c c' (by (show f.isCentre DKL; assumption)) (by (show d.onCircle DKL; assumption)) (by (show g.isCentre KLH; assumption)) (by (show h.onCircle KLH; assumption)) (by (show i.onCircle KLH; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show between d f e; assumption)) (by (show between f g e; assumption)) (by (show between g h e; assumption)) (by (show between i g h; assumption)) (by (show |(d─f)| = |(a─a')|; assumption)) (by (show |(f─g)| = |(b─b')|; assumption)) (by (show |(g─h)| = |(c─c')|; assumption)) (by (show |(a─a')| + |(b─b')| > |(c─c')|; assumption)) (by (show |(a─a')| + |(c─c')| > |(b─b')|; assumption)) (by (show |(b─b')| + |(c─c')| > |(a─a')|; assumption)))
  euclid_apply (intersection_circles KLH DKL) as k
  euclid_apply (line_from_points k f) as KF
  euclid_apply (line_from_points k g) as KG
  have s7 : distinctPointsOnLine k f KF ∧ distinctPointsOnLine k g KG := by euclid_apply (h_1_22_s7 k f g KF KG DKL KLH (by (show k.onLine KF; assumption)) (by (show f.onLine KF; assumption)) (by (show k.onLine KG; assumption)) (by (show g.onLine KG; assumption)) (by (show k.onCircle DKL; assumption)) (by (show f.isCentre DKL; assumption)) (by (show k.onCircle KLH; assumption)) (by (show g.isCentre KLH; assumption)))

  have s9_a1 : f.isCentre DKL := by assumption

  have s9 : |(f─d)| = |(f─k)| := by euclid_apply (h_1_22_s9 f d k DKL (by (show f.isCentre DKL; assumption)) (by (show d.onCircle DKL; assumption)) (by (show k.onCircle DKL; assumption)))

  have s10 : |(f─d)| = |(a─a')| := by euclid_apply (h_1_22_s10 f d a a' (by (show |(d─f)| = |(a─a')|; assumption)))

  have s11 : |(k─f)| = |(a─a')| := by euclid_apply (h_1_22_s11 k f d a a' (by (show |(f─d)| = |(f─k)|; assumption)) (by (show |(f─d)| = |(a─a')|; assumption)))

  have s12_a1 : g.isCentre KLH := by assumption

  have s12 : |(g─h)| = |(g─k)| := by euclid_apply (h_1_22_s12 g h k KLH (by (show g.isCentre KLH; assumption)) (by (show h.onCircle KLH; assumption)) (by (show k.onCircle KLH; assumption)))

  have s13 : |(g─h)| = |(c─c')| := by euclid_apply (h_1_22_s13 g h c c' (by (show |(g─h)| = |(c─c')|; assumption)))

  have s14 : |(k─g)| = |(c─c')| := by euclid_apply (h_1_22_s14 k g h c c' (by (show |(g─h)| = |(g─k)|; assumption)) (by (show |(g─h)| = |(c─c')|; assumption)))

  have s15 : |(f─g)| = |(b─b')| := by euclid_apply (h_1_22_s15 f g b b' (by (show |(f─g)| = |(b─b')|; assumption)))

  have s16 : |(k─f)| = |(a─a')| ∧ |(f─g)| = |(b─b')| ∧ |(g─k)| = |(c─c')| := by euclid_apply (h_1_22_s16 k f g a a' b b' c c' (by (show |(k─f)| = |(a─a')|; assumption)) (by (show |(f─g)| = |(b─b')|; assumption)) (by (show |(k─g)| = |(c─c')|; assumption)))

  use k, f, g
  have hgoal1 : |(f─k)| = |(a─a')| := by euclid_apply (h_1_22_x2 f k a a' (by (show |(k─f)| = |(a─a')|; assumption)))
  have hgoal2 : |(f─g)| = |(b─b')| := by euclid_apply (h_1_22_x3 f g b b' (by (show |(f─g)| = |(b─b')|; assumption)))
  have hgoal3 : |(k─g)| = |(c─c')| := by euclid_apply (h_1_22_x4 k g c c' (by (show |(k─g)| = |(c─c')|; assumption)))
  exact ⟨hgoal1, hgoal2, hgoal3⟩

end Elements.Book1
