import SystemE
import Book1.Prop04.Main
import Book1.Prop14.Main
import Book1.Prop31.Main
import Book1.Prop41.Main
import Book1.Prop17.Main
import Book1.Prop13.Main
import Book1.Prop29.Main
import Book1.Prop30.Main
import Book1Variants.Prop46

set_option systemE.solverTime 120
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Elements.Book1

theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_intro_sentence "1.47.0"
    "In right-angled triangles,  the square on the side subtending the right-angle is equal to the (sum of the) squares on the sides containing the right-angle.  Let $ABC$ be a right-angled triangle having the angle $BAC$a right-angle. I say that the square on $BC$ is equal to the (sum of the) squares on $BA$ and $AC$. "

  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_sentence "1.47.1"
    "For let the square $BDEC$ have been described on $BC$, and (the squares) $GB$ and $HC$ on $AB$ and $AC$ (respectively) [Prop.~1.46]."
    (step1 :
      (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
        (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
      (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
        (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
      (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
        (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟))) := by
    euclid_finish

  have hoffBD : ¬(a.onLine BD) := by
    intro ha
    have hbad : between a b d := by euclid_finish
    euclid_apply (proposition_17 c a b AC AB BC)
    euclid_finish
  euclid_apply (proposition_31 a b d BD) as AL
  have hALDE : AL.intersectsLine DE := by euclid_finish
  euclid_apply (intersection_lines AL DE) as l
  euclid_sentence "1.47.2"
    "And let $AL$ have been drawn through point $A$ parallel to either of $BD$ or $CE$ [Prop.~1.31]."
    (step2 : a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE))) := by
    euclid_finish

  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_sentence "1.47.3"
    "And let $AD$ and $FC$ have been joined."
    (step3 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC) := by
    euclid_finish

  -- @assumption_valid
  have step4_assumption1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟) := by euclid_finish
  -- @assumption ("angles $BAC$ and $BAG$ are each right-angles", (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟))
  euclid_sentence "1.47.4"
    "And since angles $BAC$ and $BAG$ are each right-angles, then two straight-lines $AC$ and $AG$, not lying on the same side, make the adjacent angles with some straight-line $BA$, at the point $A$ on it, (whose sum is) equal to two right-angles."
    (step4 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟)) := by
    refine (fun h => ?_) step4_assumption1
    euclid_finish

  euclid_sentence "1.47.5"
    "Thus, $CA$ is straight-on to $AG$ [Prop.~1.14]."
    (step5 : between c a g) := by
    euclid_apply (proposition_14 b a c g AB AC AG)
    euclid_finish

  euclid_sentence "1.47.6"
    "So, for the same (reasons), $BA$ is also straight-on to $AH$."
    (step6 : between b a h) := by
    euclid_apply (proposition_14 c a b h AC AB AH)
    euclid_finish

  -- @assumption_valid
  have step7_assumption1 : ∠ d:b:c = ∠ f:b:a := by euclid_finish
  -- @assumption_valid
  have step7_assumption2 : (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟) := by euclid_finish
  -- @assumption ("angle $DBC$ is equal to $FBA$", ∠ d:b:c = ∠ f:b:a)
  -- @assumption ("for (they are) both right-angles", (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟))
  euclid_sentence "1.47.7"
    "And since angle $DBC$ is equal to $FBA$, for (they are) both right-angles, let $ABC$ have been added to both. "
    (step7 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) := by
    refine (fun h1 h2 => ?_) step7_assumption1 step7_assumption2
    euclid_finish

  -- Configuration: the foot M of AL on BC lies strictly between B and C, so A and C
  -- are on the same side of BD (licences the angle addition ∠DBA = ∠DBC + ∠ABC below).
  have hALBC : AL.intersectsLine BC := by euclid_finish
  euclid_apply (intersection_lines AL BC) as m
  euclid_apply (extend_point BD d b) as d2
  euclid_apply (extend_point BC b m) as pX
  euclid_apply (extend_point BC m b) as pY
  euclid_apply (extend_point CE e c) as e2
  euclid_apply (extend_point BC c m) as pXc
  euclid_apply (extend_point BC m c) as pYc
  have hoffl : a.opposingSides l BC := by euclid_finish
  euclid_apply (pasch_4 a m l BC AL)
  have h_aml : between a m l := by euclid_finish
  euclid_apply (proposition_30 AL CE BD)
  have hALCE : ¬(AL.intersectsLine CE) := by euclid_finish
  -- AL ⊥ BC at M (corresponding angles with the parallels BD and CE): ∠AMB = ∠AMC = ∟.
  euclid_apply (proposition_29 a l d2 d pX pY m b AL BD BC)
  euclid_apply (proposition_29 a l e2 e pXc pYc m c AL CE BC)
  euclid_apply (proposition_17 a m b AL BC AB)
  euclid_apply (proposition_17 a m c AL BC AC)
  euclid_apply (proposition_17 c a b AC AB BC)
  euclid_apply (proposition_17 b a c AB AC BC)
  have h_bmc : between b m c := by
    have htri : between b m c ∨ between m b c ∨ between b c m := by euclid_finish
    rcases htri with hh | hh | hh
    · exact hh
    · exfalso
      euclid_apply (proposition_13 a b c m AB BC)
      euclid_finish
    · exfalso
      euclid_apply (proposition_13 a c b m AC BC)
      euclid_finish
  euclid_apply (pasch_2 b m c BD)
  have h_ac_bd : a.sameSide c BD := by euclid_finish

  euclid_sentence "1.47.8"
    "Thus, the whole (angle) $DBA$ is equal to the whole (angle) $FBC$."
    (step8 : ∠ d:b:a = ∠ f:b:c) := by
    euclid_apply (sum_angles_onlyif b d a c BD AB)
    euclid_apply (sum_angles_onlyif b f c a BF BC)
    euclid_finish

  -- @assumption_valid
  have step9_assumption1 : |(d─b)| = |(b─c)| := by euclid_finish
  -- @assumption_valid
  have step9_assumption2 : |(f─b)| = |(b─a)| := by euclid_finish
  -- @assumption ("$DB$ is equal to $BC$", |(d─b)| = |(b─c)|)
  -- @assumption ("$FB$ to $BA$", |(f─b)| = |(b─a)|)
  euclid_sentence "1.47.9"
    "And since $DB$ is equal to $BC$, and $FB$ to $BA$, the two (straight-lines) $DB$, $BA$ are equal to the two (straight-lines) $CB$, $BF$, respectively."
    (step9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|) := by
    refine (fun h1 h2 => ?_) step9_assumption1 step9_assumption2
    euclid_finish

  euclid_sentence "1.47.10"
    "And angle $DBA$ (is) equal to angle $FBC$."
    (step10 : ∠ d:b:a = ∠ f:b:c) := by
    euclid_finish

  euclid_sentence "1.47.11"
    "Thus, the base $AD$ [is] equal to the base $FC$,"
    (step11 : |(a─d)| = |(f─c)|) := by
    euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
    euclid_finish

  euclid_sentence "1.47.12"
    "and the triangle $ABD$ is equal to the triangle $FBC$ [Prop.~1.4]."
    (step12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) := by
    euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
    euclid_finish

  -- @assumption_valid
  have step13_assumption1 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL) := by euclid_finish
  -- @assumption ("they have the same base, $BD$, and are between the same parallels, $BD$ and $AL$", b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL))
  euclid_sentence "1.47.13"
    "And  parallelogram $BL$ [is] double (the area) of triangle $ABD$. For they have the same base, $BD$, and are between the same parallels, $BD$ and $AL$  [Prop.~1.41]."
    (step13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d) := by
    refine (fun h => ?_) step13_assumption1
    euclid_apply (proposition_41 m b d l a AL BD BC DE AB AD)
    euclid_finish

  -- @assumption_valid
  have step14_assumption1 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC) := by euclid_finish
  -- @assumption ("they have the same base, $FB$, and are between the same parallels, $FB$ and $GC$", f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC))
  euclid_sentence "1.47.14"
    "And  square $GB$ is double (the area) of triangle $FBC$. For again they have the same base, $FB$, and are between the same parallels, $FB$ and $GC$ [Prop.~1.41]."
    (step14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by
    refine (fun h => ?_) step14_assumption1
    euclid_apply (proposition_41 g f b a c AG BF GF AB FC BC)
    euclid_finish

  euclid_sentence "1.47.15"
    "[And the doubles of equal things are equal to one another.]"
    (step15 : Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by
    euclid_finish

  euclid_sentence "1.47.16"
    "Thus, the parallelogram $BL$ is also equal to the square $GB$."
    (step16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b) := by
    euclid_finish

  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  -- Symmetric configuration on the C-side: A and B are on the same side of CE.
  euclid_apply (pasch_2 c m b CE)
  have h_ab_ce : a.sameSide b CE := by euclid_finish
  euclid_sentence "1.47.17"
    "So, similarly, $AE$ and $BK$ being joined,  the parallelogram $CL$ can be shown (to be)  equal to the square $HC$."
    (step17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
    euclid_apply (sum_angles_onlyif c e a b CE AC)
    euclid_apply (sum_angles_onlyif c k b a CK BC)
    euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
    euclid_apply (proposition_41 m c e l a AL CE BC DE AC AE)
    euclid_apply (proposition_41 a c k h b AH CK AC HK BC BK)
    euclid_finish

  euclid_sentence "1.47.18"
    "Thus, the whole square $BDEC$ is equal to the (sum of the) two squares $GB$ and $HC$."
    (step18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c)) := by
    euclid_apply (pasch_3 b m c AL)
    euclid_apply (pasch_4 d l e AL DE)
    have h_dle : between d l e := by euclid_finish
    euclid_apply (sum_parallelograms_area d e b c l m DE BC BD CE)
    have hb1 : Triangle.area △ d:b:m + Triangle.area △ d:m:l =
      Triangle.area △ b:m:l + Triangle.area △ b:l:d := by euclid_finish
    have hb2 : Triangle.area △ l:m:c + Triangle.area △ l:c:e =
      Triangle.area △ c:e:l + Triangle.area △ c:l:m := by euclid_finish
    have hb3 : Triangle.area △ d:b:c + Triangle.area △ d:c:e =
      Triangle.area △ b:d:e + Triangle.area △ b:e:c := by euclid_finish
    euclid_finish

  euclid_sentence "1.47.19"
    "And the square $BDEC$ is described on $BC$,"
    (step19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|) := by
    euclid_apply (rectangle_area d e b c DE BC BD CE)
    euclid_finish

  euclid_sentence "1.47.20"
    "and the (squares) $GB$ and $HC$ on $BA$ and $AC$ (respectively)."
    (step20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|)) := by
    euclid_apply (rectangle_area g f a b GF AB AG BF)
    euclid_apply (rectangle_area h k a c HK AC AH CK)
    clear step14 step16 step17 step18
    refine ⟨?_, ?_⟩
    · have ea1 : Triangle.area △ a:g:f = Triangle.area △ f:g:a := by euclid_finish
      have ea2 : Triangle.area △ a:f:b = Triangle.area △ f:b:a := by euclid_finish
      euclid_finish
    · have eb1 : Triangle.area △ a:h:k = Triangle.area △ k:h:a := by euclid_finish
      have eb2 : Triangle.area △ a:k:c = Triangle.area △ k:c:a := by euclid_finish
      euclid_finish

  euclid_sentence "1.47.21"
    "Thus, the square on the side $BC$ is equal to the (sum of the) squares on the sides $BA$ and $AC$. "
    (step21 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by
    euclid_finish

  exact step21
  euclid_conclude_sentence "1.47.22"
    "Thus, in right-angled triangles,  the square on the side subtending the right-angle is equal to the (sum of the) squares on the sides surrounding the right-[angle]. (Which is) the very thing it was required to show."

end Elements.Book1
