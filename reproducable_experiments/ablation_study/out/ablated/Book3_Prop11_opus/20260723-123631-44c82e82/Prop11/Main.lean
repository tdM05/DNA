import SystemE
import Book1.Prop20.Main
import Book3.Prop11.step1
import Book3.Prop11.step2
import Book3.Prop11.step3
import Book3.Prop11.step4
import Book3.Prop11.step5
import Book3.Prop11.step6
import Book3.Prop11.step7
import Book3.Prop11.step8
import Book3.Prop11.step9

namespace Elements.Book3

open Elements.Book1

theorem proposition_11 : ∀ (a f g : Point) (ABC ADE : Circle),
  a.onCircle ABC ∧ a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  g.insideCircle ABC ∧
  |(g─a)| < |(f─a)| ∧
  f.isCentre ABC ∧ g.isCentre ADE ∧
  f ≠ g →
  between f g a :=
by
  euclid_intros
  euclid_intro_sentence "3.11.0"
    "If two circles touch one another internally, and their centers are found, (then) the straight-line joining their centers, being produced, will fall upon the point of union of the circles. For let two circles, $ABC$ and $ADE$, touch one another internally at point $A$, and let the center $F$ of circle $ABC$ be found [Prop.~3.1], and (the center) $G$ of (circle) $ADE$ [Prop.~3.1]. I say that the straight-line joining $G$ to $F$, being produced, will fall on $A$."

  have habsurd1 : ¬(¬(between f g a)) := by
    intro hsuppose1
    euclid_sentence "3.11.1"
      "For (if) not (then), if possible, let it fall like $FGH$ (in the figure),"
      (step1 : ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h) := by
        euclid_apply (helper_3_11_step1 a f g ABC
          (by euclid_assumption "" (show g.insideCircle ABC; assumption))
          (by euclid_assumption "" (show f ≠ g; assumption))
          (by euclid_assumption "" (show ¬ between f g a; assumption)))
    obtain ⟨h, h_ne, h_on_ABC, h_bet_fgh⟩ := step1
    -- @euclid_gap: Euclid implicitly assumes H falls outside ADE when extending line FGH; the ¬outsideCircle cases require a separate argument not given in his text
    by_cases h_out : h.outsideCircle ADE
    · have hd_ex : ∃ d : Point, d.onCircle ADE ∧ between g d h := by
        euclid_apply (line_from_points g h) as GH
        euclid_apply (intersection_circle_line_between_points ADE GH g h) as d
        exact ⟨d, by euclid_finish, by euclid_finish⟩
      obtain ⟨d, hd_on_ADE, hd_bet_gdh⟩ := hd_ex
      euclid_apply (line_from_points a f) as AF
      euclid_apply (line_from_points a g) as AG
      euclid_sentence "3.11.2"
        "and let $AF$ and $AG$ be joined."
        (step2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG) := by
          euclid_apply (helper_3_11_step2 a f g ABC ADE AF AG
            (by euclid_assumption "" (show a.onLine AF; assumption))
            (by euclid_assumption "" (show f.onLine AF; assumption))
            (by euclid_assumption "" (show a.onLine AG; assumption))
            (by euclid_assumption "" (show g.onLine AG; assumption))
            (by euclid_assumption "" (show a.onCircle ABC; assumption))
            (by euclid_assumption "" (show f.isCentre ABC; assumption))
            (by euclid_assumption "" (show a.onCircle ADE; assumption))
            (by euclid_assumption "" (show g.isCentre ADE; assumption)))
      -- triangle inequality on the genuine (non-degenerate) triangle A-G-F: a cannot lie on line
      -- FGH, since otherwise circle_line_intersections would give `between a f h`, forcing
      -- |(g─a)| > |(f─a)| and contradicting the hypothesis |(g─a)| < |(f─a)|.
      euclid_apply (line_from_points g f) as GF
      euclid_apply (proposition_20 g a f AG AF GF)
      -- @assumption_valid
      have step3_assumption1 : |(f─a)| = |(f─h)| := by euclid_finish
      -- @assumption_valid
      have step3_assumption2 : |(a─g)| + |(g─f)| > |(f─h)| := by euclid_finish
      -- @assumption ("that is to say $FH$", |(f─a)| = |(f─h)|)
      -- @assumption ("since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]", |(a─g)| + |(g─f)| > |(f─h)|)
      euclid_sentence "3.11.3"
        "Therefore, since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20], let $FG$ be taken from both."
        (step3 : |(a─g)| > |(f─h)| - |(g─f)|) := by
          euclid_apply (helper_3_11_step3 a f g h
            (by euclid_assumption "that is to say $FH$" (show |(f─a)| = |(f─h)|; assumption))
            (by euclid_assumption "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]" (show |(a─g)| + |(g─f)| > |(f─h)|; assumption)))
      euclid_sentence "3.11.4"
        "Thus, the remainder $AG$ is greater than the remainder $GH$."
        (step4 : |(a─g)| > |(g─h)|) := by
          euclid_apply (helper_3_11_step4 a f g h
            (by euclid_assumption "" (show |(a─g)| > |(f─h)| - |(g─f)|; assumption))
            (by euclid_assumption "" (show between f g h; assumption)))
      euclid_sentence "3.11.5"
        "And $AG$ (is) equal to $GD$."
        (step5 : |(a─g)| = |(g─d)|) := by
          euclid_apply (helper_3_11_step5 a g d ADE
            (by euclid_assumption "" (show g.isCentre ADE; assumption))
            (by euclid_assumption "" (show a.onCircle ADE; assumption))
            (by euclid_assumption "" (show d.onCircle ADE; assumption)))
      euclid_sentence "3.11.6"
        "Thus, $GD$ is also greater than $GH$, the lesser than the greater."
        (step6 : |(g─d)| > |(g─h)|) := by
          euclid_apply (helper_3_11_step6 a g d h
            (by euclid_assumption "" (show |(a─g)| = |(g─d)|; assumption))
            (by euclid_assumption "" (show |(a─g)| > |(g─h)|; assumption)))
      euclid_sentence "3.11.7"
        "The very thing is impossible."
        (step7 : False) := by
          euclid_apply (helper_3_11_step7 g d h ADE
            (by euclid_assumption "" (show |(g─d)| > |(g─h)|; assumption))
            (by euclid_assumption "" (show g.isCentre ADE; assumption))
            (by euclid_assumption "" (show d.onCircle ADE; assumption))
            (by euclid_assumption "" (show h.outsideCircle ADE; assumption)))
      exact step7
    · -- @euclid_gap branch: h is NOT outside ADE. Line FGH passes through g (centre of ADE), so it
      -- meets ADE at its two diameter ends d, d2. The end nearer f lands strictly inside ABC, so it is
      -- a point on ADE inside ABC; together with h (on ABC, not outside ADE) this exhibits a genuine
      -- crossing of the two circles — contradicting ¬ ABC.intersectsCircle ADE.
      have step_nhout : False := by
        euclid_apply (line_from_points f h) as FGH
        have hg_on : g.onLine FGH := by euclid_finish
        have hFGH_int : FGH.intersectsCircle ADE := by euclid_finish
        euclid_apply (intersections_circle_line ADE FGH) as (d, d2)
        euclid_finish
      exact step_nhout

  euclid_sentence "3.11.8"
    "Thus, the straight-line joining $F$ to $G$ will not fall outside (one circle but inside the other)."
    (step8 : ¬(¬(between f g a))) := by
      euclid_apply (helper_3_11_step8 a f g
        (by euclid_assumption "" (show ¬(¬(between f g a)); assumption)))

  euclid_sentence "3.11.9"
    "Thus, it will fall upon the point of union (of the circles) at point $A$."
    (step9 : between f g a) := by
      euclid_apply (helper_3_11_step9 a f g
        (by euclid_assumption "" (show ¬(¬(between f g a)); assumption)))

  exact step9
  euclid_conclude_sentence "3.11.10"
    "Thus, if two circles touch one another internally, [and their centers are found], (then) the straight-line joining their centers, [being produced], will fall upon the point of union of the circles. (Which is) the very thing it was required to show."

end Elements.Book3
