import SystemE
import Book1.Prop31.Main
import Book1Variants.Prop46
import Book1.Prop05.Main
import Book1Variants.Prop05
import Book1.Prop06.Main
import Book1.Prop29.Main
import Book1Variants.Prop29
import Book1.Prop30.Main
import Book1.Prop34.Main
import Book1Variants.Prop34
import Book1.Prop43.Main
import Mathlib.Tactic.Linarith

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 120
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

theorem proposition_4 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  euclid_intro_sentence "2.4.0"
    "If a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."

  euclid_apply (Elements.Book1.proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_sentence "2.4.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46],"
    (step1 : |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by euclid_finish

  euclid_apply (line_from_points b d) as BD
  euclid_sentence "2.4.2"
    "and let $BD$ be joined,"
    (step2 : distinctPointsOnLine b d BD) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF BD) as g
  euclid_apply (intersection_lines CF DE) as f
  euclid_sentence "2.4.3"
    "and let $CF$ be drawn through $C$, parallel to either of $AD$ or $EB$ [Prop.~1.31],"
    (step3 : c.onLine CF ∧ ¬(CF.intersectsLine AD)) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_31 g a b AB) as HK
  euclid_apply (intersection_lines HK AD) as h
  euclid_apply (intersection_lines HK BE) as k
  euclid_sentence "2.4.4"
    "and let $HK$ be drawn through $G$, parallel to either of $AB$ or $DE$ [Prop.~1.31]."
    (step4 : g.onLine HK ∧ ¬(HK.intersectsLine AB)) := by euclid_finish

  -- @assumption_valid
  have step5_assumption1 : ¬(CF.intersectsLine AD) := by assumption
  -- @assumption ("$CF$ is parallel to $AD$", ¬(CF.intersectsLine AD))
  euclid_apply (Elements.Book1.proposition_29'''' c a b g d CF AD BD)
  euclid_sentence "2.4.5"
    "And since $CF$ is parallel to $AD$, and $BD$ has fallen across them, the external angle $CGB$ is equal to the internal and opposite (angle) $ADB$ [Prop.~1.29]."
    (step5 : ∠ c:g:b = ∠ a:d:b) := by euclid_finish

  -- @assumption_valid
  have step6_assumption1 : |(a─d)| = |(a─b)| := by assumption
  -- @assumption ("the side $BA$ is also equal to $AD$", |(a─d)| = |(a─b)|)
  euclid_apply (Elements.Book1.proposition_5' a d b AD BD AB)
  euclid_sentence "2.4.6"
    "But, $ADB$ is equal to $ABD$, since the side $BA$ is also equal to $AD$ [Prop.~1.5]."
    (step6 : ∠ a:d:b = ∠ a:b:d) := by euclid_finish

  euclid_sentence "2.4.7"
    "Thus, angle $CGB$ is also equal to $GBC$."
    (step7 : ∠ c:g:b = ∠ g:b:c) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_6 c g b CF BD AB)
  euclid_sentence "2.4.8"
    "So the side $BC$ is equal to the side $CG$ [Prop.~1.6]."
    (step8 : |(b─c)| = |(c─g)|) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_30 CF BE AD)
  euclid_apply (Elements.Book1.proposition_34' c b g k AB HK CF BE)
  euclid_sentence "2.4.9"
    "But, $CB$ is equal to $GK$,"
    (step9 : |(c─b)| = |(g─k)|) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_34' c b g k AB HK CF BE)
  euclid_sentence "2.4.10"
    "and $CG$ to $KB$ [Prop.~1.34]."
    (step10 : |(c─g)| = |(k─b)|) := by euclid_finish

  euclid_sentence "2.4.11"
    "Thus, $GK$ is also equal to $KB$."
    (step11 : |(g─k)| = |(k─b)|) := by euclid_finish

  euclid_sentence "2.4.12"
    "Thus, $CGKB$ is equilateral."
    (step12 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by euclid_finish

  euclid_wts "2.4.13"
    "So I say that (it is) also right-angled."

  -- @assumption_gap
  have step14_assumption1 : ¬(CF.intersectsLine BE) := by assumption
  -- @assumption ("$CG$ is parallel to $BK$", ¬(CF.intersectsLine BE))
  euclid_apply (Elements.Book1.proposition_29''''' k g b c BE CF AB)
  euclid_sentence "2.4.14"
    "For since $CG$ is parallel to $BK$ [and the straight-line $CB$ has fallen across them], the angles $KBC$ and $GCB$ are thus equal to two right-angles [Prop.~1.29]."
    (step14 : ∠ k:b:c + ∠ g:c:b = ∟ + ∟) := by euclid_finish

  euclid_sentence "2.4.15"
    "But $KBC$ (is) a right-angle."
    (step15 : ∠ k:b:c = ∟) := by euclid_finish

  euclid_sentence "2.4.16"
    "Thus, $BCG$ (is) also a right-angle."
    (step16 : ∠ b:c:g = ∟) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_34' c b g k AB HK CF BE)
  euclid_sentence "2.4.17"
    "So the opposite (angles) $CGK$ and $GKB$ are also right-angles [Prop.~1.34]."
    (step17 : (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by euclid_finish

  euclid_sentence "2.4.18"
    "Thus, $CGKB$ is right-angled."
    (step18 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by euclid_finish

  euclid_sentence "2.4.19"
    "And it was also shown (to be) equilateral."
    (step19 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by euclid_finish

  euclid_sentence "2.4.20"
    "Thus, it is a square."
    (step20 : (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
      ((∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟))) := by euclid_finish

  euclid_apply (rectangle_area c b g k AB HK CF BE)
  euclid_sentence "2.4.21"
    "And it is on $CB$."
    (step21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_30 DE HK AB)
  have hbet_ahd : between a h d := by euclid_finish
  have hbet_dfe : between d f e := by euclid_finish
  have hbet_cgf : between c g f := by euclid_finish
  have hbet_bke : between b k e := by euclid_finish
  have hbet_acb : between a c b := by euclid_finish
  euclid_apply (Elements.Book1.proposition_34' d h f g AD CF DE HK)
  euclid_apply (Elements.Book1.proposition_34' a h c g AD CF AB HK)
  euclid_sentence "2.4.22"
    "So, for the same (reasons), $HF$ is also a square."
    (step22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟))) := by euclid_finish

  euclid_apply (Elements.Book1.proposition_34' a h c g AD CF AB HK)
  euclid_sentence "2.4.23"
    "And it is on $HG$, that is to say [on] $AC$ [Prop.~1.34]."
    (step23 : |(h─g)| = |(a─c)|) := by euclid_finish

  have hrect24 := rectangle_area d h f g AD CF DE HK
    ⟨by simp only [formParallelogram, distinctPointsOnLine]; euclid_finish, by euclid_finish⟩
  have h24d1 : |(d─h)| = |(a─c)| := by euclid_finish
  have h24d2 : |(d─f)| = |(a─c)| := by euclid_finish
  euclid_sentence "2.4.24"
    "Thus, the squares $HF$ and $KC$ are on $AC$ and $CB$ (respectively)."
    (step24 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨-, hf2⟩ := hrect24
      have hperm : Triangle.area △ h:d:f = Triangle.area △ h:f:d := by euclid_finish
      rw [h24d1, h24d2] at hf2
      linarith [hf2, hperm]
    · euclid_finish

  have hpp1 : formParallelogram b a e d AB DE BE AD := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hpp2 : formParallelogram b c k g AB HK BE CF := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hpp3 : formParallelogram g h f d HK DE CF AD := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hbdd : distinctPointsOnLine b d BD := by simp only [distinctPointsOnLine]; euclid_finish
  have hgbd : g.onLine BD := by euclid_finish
  have hbca : between b c a := by euclid_finish
  euclid_apply (Elements.Book1.proposition_43 b e d a k h f c g AB DE BE AD BD HK CF
    ⟨hpp1, hbdd, hgbd, hbca, hpp2, hpp3⟩)
  euclid_sentence "2.4.25"
    "And the (rectangle) $AG$ is equal to the (rectangle) $GE$ [Prop.~1.43]."
    (step25 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ g:k:e + Triangle.area △ g:e:f) := by euclid_finish

  -- @assumption_valid
  have step26_assumption1 : |(b─c)| = |(c─g)| := by assumption
  -- @assumption ("$GC$ (is) equal to $CB$", |(b─c)| = |(c─g)|)
  have hrect26 := rectangle_area a h c g AD CF AB HK
    ⟨by simp only [formParallelogram, distinctPointsOnLine]; euclid_finish, by euclid_finish⟩
  euclid_sentence "2.4.26"
    "And $AG$ is the (rectangle contained) by $AC$ and $CB$. For $GC$ (is) equal to $CB$."
    (step26 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) := by
    obtain ⟨hf1, -⟩ := hrect26
    have hperm : Triangle.area △ a:h:g = Triangle.area △ a:g:h := by euclid_finish
    have hlen : |(a─h)| = |(c─b)| := by euclid_finish
    have hrhs : |(a─h)| * |(a─c)| = |(a─c)| * |(c─b)| := by rw [hlen]; ring
    linarith [hf1, hperm, hrhs]

  euclid_sentence "2.4.27"
    "Thus, $GE$ is also equal to the (rectangle contained) by $AC$ and $CB$."
    (step27 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) := by euclid_finish

  euclid_sentence "2.4.28"
    "Thus, the (rectangles) $AG$ and $GE$ are equal to twice the (rectangle contained) by $AC$ and $CB$."
    (step28 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
      (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(c─b)| + |(a─c)| * |(c─b)|) := by euclid_finish

  euclid_sentence "2.4.29"
    "And $HF$ and $CK$ are the squares on $AC$ and $CB$ (respectively)."
    (step29 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by euclid_finish

  -- All helper facts are established BEFORE the `2 *`-carrying claims (step30, step33) enter the
  -- local context: `euclid_finish`'s SMT translator cannot handle the `2 *` literal, so any
  -- `euclid_finish` run with such a hypothesis in scope would abort.  These `have`s use `euclid_finish`
  -- only while the context is free of `2 *`; the sentence bodies below close by `exact`/`linarith`.
  have hpara_sq : formParallelogram a b d e AB DE AD BE := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hpara_adcf : formParallelogram a d c f AD CF AB DE := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hpara_cfbe : formParallelogram c f b e CF BE AB DE := by
    simp only [formParallelogram, distinctPointsOnLine]; euclid_finish
  have hsum31a := sum_parallelograms_area a b d e c f AB DE AD BE ⟨hpara_sq, hbet_acb, hbet_dfe⟩
  have hsum31b := sum_parallelograms_area a d c f h g AD CF AB DE ⟨hpara_adcf, hbet_ahd, hbet_cgf⟩
  have hsum31c := sum_parallelograms_area c f b e g k CF BE AB DE ⟨hpara_cfbe, hbet_cgf, hbet_bke⟩
  have hrect32 := rectangle_area a b d e AB DE AD BE ⟨hpara_sq, by euclid_finish⟩
  have h31 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b := by euclid_finish
  have h32 : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)| := by euclid_finish
  have h30 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) := by
    rw [two_mul]; euclid_finish
  euclid_sentence "2.4.30"
    "Thus, the four (figures) $HF$, $CK$, $AG$, and $GE$ are equal to the (sum of the) squares on $AC$ and $BC$, and twice the rectangle contained by $AC$ and $CB$."
    (step30 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by exact h30

  euclid_sentence "2.4.31"
    "But, the (figures) $HF$, $CK$, $AG$, and $GE$ are (equivalent to) the whole of $ADEB$,"
    (step31 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b) := by exact h31

  euclid_sentence "2.4.32"
    "which is the square on $AB$."
    (step32 : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)|) := by exact h32

  euclid_sentence "2.4.33"
    "Thus, the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."
    (step33 : |(a─b)| * |(a─b)| =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by
    linarith [h30, h31, h32]

  linarith [h30, h31, h32]
  euclid_conclude_sentence "2.4.34"
    "Thus, if a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. (Which is) the very thing it was required to show."

end Elements.Book2
