import SystemE
import Book1.Prop03.Main

namespace Elements.Book1

theorem proposition_22 : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) := by
  euclid_intros
  euclid_intro_sentence "1.22.0"
    "To construct a triangle from three straight-lines which are equal to three given [straight-lines]. It is necessary for (the sum of) two (of the straight-lines) taken together in any (possible way) to be greater than the remaining (one), on account of the (fact that) in any triangle (the sum of) two sides taken together in any (possible way) is greater than the remaining (one) [Prop.~1.20]. Let $A$, $B$, and $C$ be the three given straight-lines, of which let (the sum of) two taken together in any (possible way)  be greater than the remaining (one). (Thus), (the sum of) $A$ and $B$ (is greater) than $C$, (the sum of) $A$ and $C$ than $B$,  and also (the sum of) $B$ and $C$ than $A$. So it is required to construct a triangle  from (straight-lines) equal to $A$, $B$, and $C$.   "

  euclid_apply arbitrary_point as d
  euclid_apply (distinct_points d) as e'
  euclid_apply (line_from_points d e') as DE
  euclid_apply (extend_point_longer DE d e' (a─a')) as e''
  euclid_apply (extend_point_longer DE d e'' (b─b')) as e'''
  euclid_apply (extend_point_longer DE d e''' (c─c')) as e
  euclid_sentence "1.22.1"
    "Let some straight-line $DE$ be set out, terminated at $D$, and infinite in the  direction of $E$. "
    (step1 : distinctPointsOnLine d e DE) := by sorry

  euclid_apply (proposition_3 d e a a' DE A) as f
  euclid_sentence "1.22.2"
    "And let $DF$ made equal to $A$,"
    (step2 : |(d─f)| = |(a─a')|) := by sorry

  euclid_apply (proposition_3 f e b b' DE B) as g
  euclid_sentence "1.22.3"
    "and $FG$  equal to $B$,"
    (step3 : |(f─g)| = |(b─b')|) := by sorry

  euclid_apply (proposition_3 g e c c' DE C) as h
  euclid_sentence "1.22.4"
    "and $GH$ equal to $C$ [Prop.~1.3]."
    (step4 : |(g─h)| = |(c─c')|) := by sorry

  euclid_apply (circle_from_points f d) as DKL
  euclid_sentence "1.22.5"
    "And let the  circle $DKL$ have been drawn with center $F$ and radius $FD$."
    (step5 : f.isCentre DKL ∧ d.onCircle DKL) := by sorry

  euclid_apply (circle_from_points g h) as KLH
  euclid_sentence "1.22.6"
    "Again,  let the circle $KLH$ have been drawn with center $G$ and radius $GH$."
    (step6 : g.isCentre KLH ∧ h.onCircle KLH) := by sorry

  euclid_apply (intersection_circle_line_extending_points KLH DE g h) as i
  have hcut : KLH.intersectsCircle DKL := by sorry
  euclid_apply (intersection_circles KLH DKL) as k
  euclid_apply (line_from_points k f) as KF
  euclid_apply (line_from_points k g) as KG
  euclid_sentence "1.22.7"
    "And  let $KF$ and $KG$ have been joined."
    (step7 : distinctPointsOnLine k f KF ∧ distinctPointsOnLine k g KG) := by sorry

  euclid_wts "1.22.8"
    "I say that the triangle $KFG$ has been  constructed from three straight-lines equal to $A$, $B$, and $C$.   "

  -- @assumption_valid
  have step9_assumption1 : f.isCentre DKL := by assumption
  -- @assumption ("point $F$ is the center of the circle $DKL$", f.isCentre DKL)
  euclid_sentence "1.22.9"
    "For since point $F$ is the center of the circle $DKL$, $FD$ is equal to $FK$. "
    (step9 : |(f─d)| = |(f─k)|) := by sorry

  euclid_sentence "1.22.10"
    "But, $FD$ is equal to $A$."
    (step10 : |(f─d)| = |(a─a')|) := by sorry

  euclid_sentence "1.22.11"
    "Thus, $KF$ is also equal to $A$."
    (step11 : |(k─f)| = |(a─a')|) := by sorry

  -- @assumption_valid
  have step12_assumption1 : g.isCentre KLH := by assumption
  -- @assumption ("point  $G$ is the center of the circle $LKH$", g.isCentre KLH)
  euclid_sentence "1.22.12"
    "Again, since point  $G$ is the center of the circle $LKH$, $GH$ is equal to $GK$."
    (step12 : |(g─h)| = |(g─k)|) := by sorry

  euclid_sentence "1.22.13"
    "But, $GH$ is equal  to $C$."
    (step13 : |(g─h)| = |(c─c')|) := by sorry

  euclid_sentence "1.22.14"
    "Thus, $KG$ is also equal to $C$."
    (step14 : |(k─g)| = |(c─c')|) := by sorry

  euclid_sentence "1.22.15"
    "And $FG$ is also equal to $B$."
    (step15 : |(f─g)| = |(b─b')|) := by sorry

  euclid_sentence "1.22.16"
    "Thus,  the three straight-lines $KF$, $FG$, and $GK$ are equal to $A$, $B$, and $C$ (respectively).   "
    (step16 : |(k─f)| = |(a─a')| ∧ |(f─g)| = |(b─b')| ∧ |(g─k)| = |(c─c')|) := by sorry

  -- goal orientation (f─k, k─g) bridges step16's KF/GK (k─f, g─k) by length symmetry
  use k, f, g
  have hgoal1 : |(f─k)| = |(a─a')| := by sorry
  have hgoal2 : |(f─g)| = |(b─b')| := by sorry
  have hgoal3 : |(k─g)| = |(c─c')| := by sorry
  exact ⟨hgoal1, hgoal2, hgoal3⟩
  euclid_conclude_sentence "1.22.17"
    "Thus, the triangle $KFG$ has been constructed from the three straight-lines  $KF$, $FG$, and $GK$, which are equal to the three given straight-lines  $A$, $B$, and $C$ (respectively). (Which is) the very thing it was required  to do."

end Elements.Book1
