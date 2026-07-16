import SystemE
import Book3.Prop01.Main
import Book3.Prop17.Main

namespace Elements.Book3

theorem proposition_37 : ∀ (d a c b : Point) (ABC : Circle) (DB : Line),
  d.outsideCircle ABC ∧
  a.onCircle ABC ∧ c.onCircle ABC ∧ between d c a ∧
  b.onCircle ABC ∧ d.onLine DB ∧ b.onLine DB ∧
  |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)| →
  (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC :=
by
  euclid_intros
  euclid_intro_sentence "3.37.0"
    "If some point is taken outside a circle, and two straight-lines radiate from the point towards the circle, and one of them cuts the circle, and the (other) meets (it), and the (rectangle contained) by the whole (straight-line) cutting (the circle), and the (part of it) cut off outside (the circle), between the point and the convex circumference, is equal to the (square) on the (straight-line) meeting (the circle), (then) the (straight-line) meeting (the circle) will touch the circle. For let some point $D$ be taken outside circle $ABC$, and let two straight-lines, $DCA$ and $DB$, radiate from $D$ towards circle $ABC$, and let $DCA$ cut the circle, and let $DB$ meet (the circle). And let the (rectangle contained) by $AD$ and $DC$ be equal to the (square) on $DB$. I say that $DB$ touches circle $ABC$."

  -- Construction: draw tangent DE from D [Prop. 3.17]
  euclid_apply (proposition_17 d ABC) as DE
  -- Unpack the tangent point e from the inner existential
  have he_exists : ∃ e : Point, e.onLine DE ∧ e.onCircle ABC := by euclid_finish
  obtain ⟨e, he_onDE, he_onABC⟩ := he_exists

  euclid_sentence "3.37.1"
    "For let $DE$ be drawn touching $ABC$ [Prop. 3.17],"
    (step1 : d.onLine DE ∧ e.onLine DE ∧ e.onCircle ABC ∧ ¬ DE.intersectsCircle ABC) := by sorry

  -- Construction: find center F of circle ABC [Prop. 3.1]
  euclid_apply (proposition_1 ABC) as f

  euclid_sentence "3.37.2"
    "and let the center of the circle $ABC$ be found, and let it be (at) $F$."
    (step2 : f.isCentre ABC) := by sorry

  -- Construction: join FE, FB, FD
  have hfene : f ≠ e := by sorry
  have hfbne : f ≠ b := by sorry
  have hfdne : f ≠ d := by sorry
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f d) as FD

  euclid_sentence "3.37.3"
    "And let $FE$, $FB$, and $FD$ be joined."
    (step3 : distinctPointsOnLine f e FE ∧ distinctPointsOnLine f b FB ∧ distinctPointsOnLine f d FD) := by sorry

  -- step4: FED is a right angle [Prop. 3.18] — radius FE ⊥ tangent DE at contact point e
  euclid_sentence "3.37.4"
    "(Angle) $FED$ is thus a right-angle [Prop.~3.18]."
    (step4 : ∠ f:e:d = ∟) := by sorry

  -- @assumption_valid
  have step5_assumption1 : (∃ p : Point, p.onLine DE ∧ p.onCircle ABC) ∧ ¬ DE.intersectsCircle ABC := by euclid_finish
  -- @assumption_gap
  have step5_assumption2 : ∃ DCA : Line, d.onLine DCA ∧ c.onLine DCA ∧ a.onLine DCA ∧ DCA.intersectsCircle ABC := by sorry
  -- @assumption ("$DE$ touches circle $ABC$", (∃ p : Point, p.onLine DE ∧ p.onCircle ABC) ∧ ¬ DE.intersectsCircle ABC)
  -- @assumption ("$DCA$ cuts (it)", ∃ DCA : Line, d.onLine DCA ∧ c.onLine DCA ∧ a.onLine DCA ∧ DCA.intersectsCircle ABC)
  euclid_sentence "3.37.5"
    "And since $DE$ touches circle $ABC$, and $DCA$ cuts (it), the (rectangle contained) by $AD$ and $DC$ is thus equal to the (square) on $DE$ [Prop.~3.36]."
    (step5 : |(a─d)| * |(d─c)| = |(d─e)| * |(d─e)|) := by sorry

  euclid_sentence "3.37.6"
    "And the (rectangle contained) by $AD$ and $DC$ was also equal to the (square) on $DB$."
    (step6 : |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)|) := by sorry

  euclid_sentence "3.37.7"
    "Thus, the (square) on $DE$ is equal to the (square) on $DB$."
    (step7 : |(d─e)| * |(d─e)| = |(d─b)| * |(d─b)|) := by sorry

  euclid_sentence "3.37.8"
    "Thus, $DE$ (is) equal to $DB$."
    (step8 : |(d─e)| = |(d─b)|) := by sorry

  -- step9: FE = FB because both are radii of circle ABC (f is the center)
  euclid_sentence "3.37.9"
    "And $FE$ is also equal to $FB$."
    (step9 : |(f─e)| = |(f─b)|) := by sorry

  -- step10: the "respectively equal" summary preparing the SSS setup for Prop 1.8
  euclid_sentence "3.37.10"
    "So the two (straight-lines) $DE$, $EF$ are equal to the two (straight-lines) $DB$, $BF$ (respectively)."
    (step10 : |(d─e)| = |(d─b)| ∧ |(e─f)| = |(b─f)|) := by sorry

  euclid_sentence "3.37.11"
    "And their base, $FD$, is common."
    (step11 : distinctPointsOnLine f d FD) := by sorry

  euclid_sentence "3.37.12"
    "Thus, angle $DEF$ is equal to angle $DBF$ [Prop.~1.8]."
    (step12 : ∠ d:e:f = ∠ d:b:f) := by sorry

  euclid_sentence "3.37.13"
    "And $DEF$ (is) a right-angle."
    (step13 : ∠ d:e:f = ∟) := by sorry

  euclid_sentence "3.37.14"
    "Thus, $DBF$ (is) also a right-angle."
    (step14 : ∠ d:b:f = ∟) := by sorry

  euclid_sentence "3.37.15"
    "And $FB$ produced is a diameter,"
    (step15 : ∃ g : Point, f.isCentre ABC ∧ between g f b ∧ g.onCircle ABC ∧ b.onCircle ABC) := by sorry

  euclid_sentence "3.37.16"
    "And a (straight-line) drawn at right-angles to a diameter of a circle, at its extremity, touches the circle [Prop.~3.16~corr.]."
    (step16 : ∀ (p q r : Point) (γ : Circle) (L : Line),
        r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ →
        (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ) := by sorry

  -- step17: the main conclusion — DB touches ABC
  euclid_sentence "3.37.17"
    "Thus, $DB$ touches circle $ABC$."
    (step17 : (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC) := by sorry

  euclid_sentence "3.37.18"
    "Similarly, (the same thing) can be shown, even if the center happens to be on $AC$."
    (step18 : collinear d f c →
        (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC) := by sorry

  exact step17
  euclid_conclude_sentence "3.37.19"
    "Thus, if some point is taken outside a circle, and two straight-lines radiate from the point towards the circle, and one of them cuts the circle, and the (other) meets (it), and the (rectangle contained) by the whole (straight-line) cutting (the circle), and the (part of it) cut off outside (the circle), between the point and the convex circumference, is equal to the (square) on the (straight-line) meeting (the circle), (then) the (straight-line) meeting (the circle) will touch the circle. (Which is) the very thing it was required to show."

end Elements.Book3
