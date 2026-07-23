import SystemE
import Book1.Prop04.Main
import Book1.Prop14.Main
import Book1.Prop31.Main
import Book1.Prop41.Main
import Book1Variants.Prop46

namespace Elements.Book1

theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)

  have hoffBD : ¬(a.onLine BD) := by euclid_finish
  euclid_apply (proposition_31 a b d BD) as AL
  have hALDE : AL.intersectsLine DE := by euclid_finish
  euclid_apply (intersection_lines AL DE) as l
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  have hALBC : AL.intersectsLine BC := by euclid_finish
  euclid_apply (intersection_lines AL BC) as m
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK

  -- step8 sameSides
  have hs8_1 : d.sameSide c AB := by euclid_finish
  have hs8_2 : a.sameSide c BD := by euclid_finish
  have hs8_3 : f.sameSide a BC := by euclid_finish
  have hs8_4 : c.sameSide a BF := by euclid_finish

  -- squares as parallelograms
  have hpara_sqBC : formParallelogram d e b c DE BC BD CE := by euclid_finish
  have hpara_sqAB : formParallelogram g f a b GF AB AG BF := by euclid_finish
  have hpara_sqAC : formParallelogram h k a c HK AC AH CK := by euclid_finish

  -- step13
  have hpara_BL : formParallelogram l m d b AL BD DE BC := by euclid_finish
  have htri_BL : formTriangle a d b AD BD AB := by euclid_finish

  -- step14
  have hcAG : c.onLine AG := by euclid_finish
  have hpara_GB : formParallelogram a g b f AG BF AB GF := by euclid_finish
  have htri_GB : formTriangle c b f BC BF FC := by euclid_finish

  -- step17
  have hbAH : b.onLine AH := by euclid_finish
  have hALCE : ¬(AL.intersectsLine CE) := by euclid_finish
  have hpara_CL : formParallelogram l m e c AL CE DE BC := by euclid_finish
  have htri_CL : formTriangle a e c AE CE AC := by euclid_finish
  have hpara_HC : formParallelogram a h c k AH CK AC HK := by euclid_finish
  have htri_HC : formTriangle b c k BC CK BK := by euclid_finish
  have hangC : ∠ e:c:a = ∠ b:c:k := by euclid_finish

  -- step18
  have hbmc : between b m c := by euclid_finish
  have hdle : between d l e := by euclid_finish

  have hsplit : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ b:m:l + Triangle.area △ b:l:d) +
      (Triangle.area △ c:e:l + Triangle.area △ c:l:m) := by euclid_finish

  euclid_intro_sentence "1.47.0" "x"
  euclid_sentence "1.47.1" "x"
    (step1 :
      (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
        (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
      (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
        (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
      (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
        (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟))) := by sorry
  euclid_sentence "1.47.2" "x"
    (step2 : a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE))) := by sorry
  euclid_sentence "1.47.3" "x"
    (step3 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC) := by sorry
  euclid_sentence "1.47.4" "x"
    (step4 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟)) := by sorry
  euclid_sentence "1.47.5" "x"
    (step5 : between c a g) := by sorry
  euclid_sentence "1.47.6" "x"
    (step6 : between b a h) := by sorry
  euclid_sentence "1.47.7" "x"
    (step7 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) := by sorry
  euclid_sentence "1.47.8" "x"
    (step8 : ∠ d:b:a = ∠ f:b:c) := by sorry
  euclid_sentence "1.47.9" "x"
    (step9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|) := by sorry
  euclid_sentence "1.47.10" "x"
    (step10 : ∠ d:b:a = ∠ f:b:c) := by sorry
  euclid_sentence "1.47.11" "x"
    (step11 : |(a─d)| = |(f─c)|) := by sorry
  euclid_sentence "1.47.12" "x"
    (step12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) := by sorry
  euclid_sentence "1.47.13" "x"
    (step13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d) := by sorry
  euclid_sentence "1.47.14" "x"
    (step14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by sorry
  euclid_sentence "1.47.15" "x"
    (step15 : Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by sorry
  euclid_sentence "1.47.16" "x"
    (step16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b) := by sorry
  euclid_sentence "1.47.17" "x"
    (step17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by sorry
  euclid_sentence "1.47.18" "x"
    (step18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c)) := by sorry
  euclid_sentence "1.47.19" "x"
    (step19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|) := by sorry
  euclid_sentence "1.47.20" "x"
    (step20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|)) := by sorry
  euclid_sentence "1.47.21" "x"
    (step21 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by sorry

  exact step21

end Elements.Book1
