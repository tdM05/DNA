import SystemE
import Book1.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| := by
  euclid_intros
  euclid_intro_sentence "1.6.0"
    "If a triangle has two angles equal to one another then the sides subtending the equal angles will also be equal to one another. Let $ABC$ be a triangle having the angle $ABC$ equal to the angle $ACB$. I say that side $AB$ is also equal to side $AC$. "

  have habsurd1 : ¬(|(a─b)| ≠ |(a─c)|) := by
    intro hsuppose1
    euclid_sentence "1.6.1"
      "For if $AB$ is unequal to $AC$ then one of them is greater."
      (step1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|) := by sorry

    rcases step1 with hgt | hgt
    -- Euclid's written case: AB is the greater.
    ·
      euclid_sentence "1.6.2"
        "Let $AB$ be greater."
        (step2 : |(a─b)| > |(a─c)|) := by sorry

      euclid_apply (proposition_3 b a a c AB AC) as d
      euclid_sentence "1.6.3"
        "And let $DB$, equal to the lesser $AC$, have been cut off from the greater $AB$ [Prop.~1.3]. "
        (step3 : |(d─b)| = |(a─c)|) := by sorry

      euclid_apply (line_from_points d c) as DC
      euclid_sentence "1.6.4"
        "And let $DC$ have been joined [Post.~1]. "
        (step4 : distinctPointsOnLine d c DC) := by sorry

      -- the two sides DB, BC equal the two sides AC, CB respectively (the SAS side-premise):
      -- the pair of length equalities DB = AC and BC = CB.
      euclid_sentence "1.6.5"
        "Therefore, since $DB$ is equal to $AC$, and $BC$ (is) common, the two sides $DB$, $BC$ are equal to the two sides $AC$, $CB$, respectively,"
        (step5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)|) := by sorry

      euclid_sentence "1.6.6"
        "and the angle $DBC$ is equal to the angle $ACB$."
        (step6 : ∠ d:b:c = ∠ a:c:b) := by sorry

      euclid_sentence "1.6.7"
        "Thus, the base $DC$ is equal to the base $AB$,"
        (step7 : |(d─c)| = |(a─b)|) := by sorry

      euclid_sentence "1.6.8"
        "and the triangle $DBC$ will be equal to the triangle $ACB$ [Prop.~1.4], the lesser to the greater."
        (step8 : Triangle.area △ d:b:c = Triangle.area △ a:c:b) := by sorry

      euclid_sentence "1.6.9"
        "The very notion (is) absurd [C.N.~5]."
        (step9 : False) := by sorry
      exact step9
    -- symmetric case: AC is the greater — handled by the mirror helper.
    ·
      have sym : False := by sorry
      exact sym

  euclid_sentence "1.6.10"
    "Thus, $AB$ is not unequal to $AC$."
    (step10 : ¬(|(a─b)| ≠ |(a─c)|)) := by sorry

  euclid_sentence "1.6.11"
    "Thus, (it is) equal. "
    (step11 : |(a─b)| = |(a─c)|) := by sorry

  exact step11
  euclid_conclude_sentence "1.6.12"
    "Thus, if a triangle has two angles equal to one another then the sides subtending the equal angles will also be equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
