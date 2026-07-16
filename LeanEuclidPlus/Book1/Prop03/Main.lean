import SystemE
import Book1Variants.Prop02

namespace Elements.Book1

theorem proposition_3 : ∀ (a b c₀ c₁ : Point) (AB C : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c₀ c₁ C ∧ |(a─b)| > |(c₀─c₁)| →
  ∃ e : Point, between a e b ∧ |(a─e)| = |(c₀─c₁)| := by
  euclid_intros
  euclid_intro_sentence "1.3.0"
    "For two given unequal straight-lines, to cut off from the greater a straight-line equal to the lesser.  Let $AB$ and $C$ be the two given unequal straight-lines, of which let the greater be $AB$. So it is required to cut off a straight-line equal to the lesser $C$ from the greater $AB$. "

  euclid_apply (proposition_2' a c₀ c₁ C) as d
  euclid_sentence "1.3.1"
    "Let the line $AD$, equal to the straight-line $C$, have been placed at  point $A$ [Prop.~1.2]."
    (step1 : |(a─d)| = |(c₀─c₁)|) := by euclid_finish

  euclid_apply (circle_from_points a d) as DEF
  euclid_apply (intersection_circle_line_between_points DEF AB a b) as e
  euclid_sentence "1.3.2"
    "And let the circle $DEF$ have been drawn with center $A$ and radius $AD$ [Post.~3]. "
    (step2 : a.isCentre DEF ∧ d.onCircle DEF) := by euclid_finish

  -- @assumption_valid
  have step3_assumption1 : a.isCentre DEF := by assumption
  -- @assumption ("point $A$ is the center of  circle $DEF$", a.isCentre DEF)
  euclid_sentence "1.3.3"
    "And since  point $A$ is the center of  circle $DEF$, $AE$ is equal to $AD$ [Def.~1.15]."
    (step3 : |(a─e)| = |(a─d)|) := by euclid_finish

  euclid_sentence "1.3.4"
    "But, $C$ is also equal to $AD$."
    (step4 : |(c₀─c₁)| = |(a─d)|) := by euclid_finish

  euclid_sentence "1.3.5"
    "Thus, $AE$ and $C$ are each equal to $AD$."
    (step5 : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)|) := by euclid_finish

  euclid_sentence "1.3.6"
    "So $AE$ is also equal to $C$ [C.N.~1]."
    (step6 : |(a─e)| = |(c₀─c₁)|) := by euclid_finish

  use e
  euclid_conclude_sentence "1.3.7"
    "Thus, for two given unequal straight-lines, $AB$ and $C$, the (straight-line) $AE$, equal to the lesser $C$, has been cut off from the greater $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
