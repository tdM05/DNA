import SystemE

namespace Elements.Book3

-- III.26. "In equal circles, equal angles stand upon equal circumferences whether they
-- are standing at the center or at the circumference." Faithful STATEMENT ONLY (body sorry).
--
-- Now stated with the Arc sort: the goal is the LITERAL conclusion `circumference BKC =
-- circumference ELF`, i.e. `⌒ b:k:c = ⌒ e:l:f` — NOT the central-angle proxy the pre-Arc
-- version was forced into.
--
-- k, l are Euclid's arc-labels K, L: a point naming WHICH arc. The angle at a stands on the
-- arc NOT containing a, so k is pinned by `opposingSides a k BC` (k on the far side of the
-- chord BC from a) together with `k.onCircle ABC`; likewise l with `opposingSides d l EF`.
-- The chord lines BC, EF are binders because the disambiguation names them.
--
-- Both angle equalities are given (central ∠b:g:c=∠e:h:f AND inscribed ∠b:a:c=∠e:d:f),
-- mirroring Euclid's setup; his proof uses the central pair for SAS (BC=EF) and the
-- inscribed pair for the similar-segments step.
theorem proposition_26 : ∀ (a b c d e f g h k l : Point) (BC EF : Line) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧ k.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧ f.onCircle DEF ∧ l.onCircle DEF ∧
  g.isCentre ABC ∧ h.isCentre DEF ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  |(g─b)| = |(h─e)| ∧                                -- equal circles (= equal radii, Def 3.1)
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
  a.opposingSides k BC ∧ d.opposingSides l EF ∧      -- k, l on the arc the angle stands on
  ∠ b:g:c = ∠ e:h:f ∧                                -- equal angles at the center
  ∠ b:a:c = ∠ e:d:f →                                -- equal angles at the circumference
  ⌒ b:k:c = ⌒ e:l:f :=
by
  euclid_intros
  euclid_intro_sentence "3.26.0"
    "In equal circles, equal angles stand upon equal circumferences whether they are standing at the center or at the circumference. Let $ABC$ and $DEF$ be equal circles, and within them let $BGC$ and $EHF$ be equal angles at the center, and $BAC$ and $EDF$ (equal angles) at the circumference. I say that circumference $BKC$ is equal to circumference $ELF$."

  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points e f) as EF
  euclid_sentence "3.26.1"
    "For let $BC$ and $EF$ be joined."
    (step1 : distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF) := by sorry

  -- @assumption ("circles $ABC$ and $DEF$ are equal", |(g─b)| = |(h─e)|)
  euclid_sentence "3.26.2"
    "And since circles $ABC$ and $DEF$ are equal, their radii are equal."
    (step2 : |(g─b)| = |(h─e)| ∧ |(g─c)| = |(h─f)|) := by sorry

  euclid_sentence "3.26.3"
    "So the two (straight-lines) $BG$, $GC$ (are) equal to the two (straight-lines) $EH$, $HF$ (respectively)."
    (step3 : |(g─b)| = |(h─e)| ∧ |(g─c)| = |(h─f)|) := by sorry

  -- "the angle at G = the angle at H" — the equal central angles, now a GIVEN of the signature
  -- (∠b:g:c=∠e:h:f, matching Euclid's "let BGC, EHF be equal angles at the center").
  euclid_sentence "3.26.4"
    "And the angle at $G$ (is) equal to the angle at $H$."
    (step4 : ∠ b:g:c = ∠ e:h:f) := by sorry

  euclid_sentence "3.26.5"
    "Thus, the base $BC$ is equal to the base $EF$ [Prop.~1.4]."
    (step5 : |(b─c)| = |(e─f)|) := by sorry

  -- @assumption ("the angle at $A$ is equal to the (angle) at $D$", ∠ b:a:c = ∠ e:d:f)
  -- "segment BAC is similar to segment EDF [Def 3.11]." Def 3.11 DEFINES similar segments as
  -- those "accepting equal angles" — so the faithful content of this sentence IS the inscribed
  -- angle equality ∠b:a:c=∠e:d:f. This is not a proxy: it is exactly what Def 3.11 unfolds to.
  euclid_sentence "3.26.6"
    "And since the angle at $A$ is equal to the (angle) at $D$, the segment $BAC$ is thus similar to the segment $EDF$ [Def.~3.11]."
    (step6 : ∠ b:a:c = ∠ e:d:f) := by sorry

  euclid_sentence "3.26.7"
    "And they are on equal straight-lines [$BC$ and $EF$]."
    (step7 : |(b─c)| = |(e─f)|) := by sorry

  -- "similar segments on equal straight-lines are equal [III.24]." Now the LITERAL segment-area
  -- equality via the CircularSegment sort: ⌓ b:a:c = ⌓ e:d:f (segment BAC = segment EDF). The
  -- [Prop.~3.24] citation is honest — III.24 is a genuine dependency (proved by circle-super-
  -- position, which Phase B will need); it is a real deferred gap, NOT a suppress case.
  euclid_sentence "3.26.8"
    "And similar segments of circles on equal straight-lines are equal to one another [Prop.~3.24]."
    (step8 : ⌓ b:a:c = ⌓ e:d:f) := by sorry

  -- "segment BAC = segment EDF" — the conclusion of applying III.24 here: equal segment areas.
  euclid_sentence "3.26.9"
    "Thus, segment $BAC$ is equal to (segment) $EDF$."
    (step9 : ⌓ b:a:c = ⌓ e:d:f) := by sorry

  -- "the whole circle ABC = the whole circle DEF." By Def 3.1 ("equal circles are those whose
  -- radii are equal") the faithful content of circle-equality IS radius equality; that is the
  -- given |(g─b)|=|(h─e)|. Euclid uses this whole-circle equality, minus the equal segments
  -- (step9), to leave the equal remaining arcs (step11).
  euclid_sentence "3.26.10"
    "And the whole circle $ABC$ is also equal to the whole circle $DEF$."
    (step10 : |(g─b)| = |(h─e)|) := by sorry

  -- "remaining circumference BKC = ELF": now the LITERAL arc equality (the goal), no longer the
  -- central-angle proxy. Euclid derives it by C.N.3 — equal WHOLE circles (step10) minus equal
  -- segments-on-BC/EF (step9) leaves the equal remaining pieces. With arcs this is: the whole
  -- circumference = (arc through a) + (arc through k) [complementary arcs on chord BC]; equal
  -- circles + equal major arcs (step9) ⟹ equal minor arcs BKC, ELF. This is the step that will
  -- need the complementary-arc / whole-circumference AXIOM (to be added).
  euclid_sentence "3.26.11"
    "Thus, the remaining circumference $BKC$ is equal to the (remaining) circumference $ELF$."
    (step11 : ⌒ b:k:c = ⌒ e:l:f) := by sorry

  exact step11
  euclid_conclude_sentence "3.26.12"
    "Thus, in equal circles, equal angles stand upon equal circumferences, whether they are standing at the center or at the circumference. (Which is) the very thing which it was required to show."


end Elements.Book3
