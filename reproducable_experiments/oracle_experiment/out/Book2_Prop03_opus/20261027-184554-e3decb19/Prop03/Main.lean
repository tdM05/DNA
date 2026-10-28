import SystemE
import Book1.Prop46.Main
import Book1.Prop31.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem proposition_3 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  euclid_intros
  euclid_intro_sentence "2.3.0"
    "If a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."

  euclid_apply (Elements.Book1.proposition_46 c b AB) as (d, e, DE, CD, BE)
  euclid_sentence "2.3.1"
    "For let the square $CDEB$ be described on $CB$ [Prop.~1.46],"
    (step1 : formParallelogram d e c b DE AB CD BE ∧
      |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧ ∠ b:c:d = ∟) := by sorry

  -- AF (the parallel through A, step 2.3.3) is what pins F, so it is built here, before F is cut.
  euclid_apply (Elements.Book1.proposition_31 a c d CD) as AF
  euclid_apply (intersection_lines AF DE) as f
  euclid_sentence "2.3.2"
    "and let $ED$ be drawn through to $F$,"
    (step2 : f.onLine DE ∧ between e d f) := by sorry

  euclid_sentence "2.3.3"
    "and let $AF$ be drawn through $A$, parallel to either of $CD$ or $BE$ [Prop.~1.31]."
    (step3 : a.onLine AF ∧ (¬(AF.intersectsLine CD) ∨ ¬(AF.intersectsLine BE))) := by sorry

  euclid_sentence "2.3.4"
    "So the (rectangle) $AE$ is equal to the (rectangle) $AD$ and the (square) $CE$."
    (step4 : Triangle.area △ a:b:e + Triangle.area △ a:e:f =
      (Triangle.area △ a:c:d + Triangle.area △ a:d:f) +
      (Triangle.area △ c:b:e + Triangle.area △ c:e:d)) := by sorry

  -- @assumption_valid
  have step5_assumption1 : |(b─e)| = |(b─c)| := by euclid_finish
  -- @assumption ("$BE$ (is) equal to $BC$", |(b─e)| = |(b─c)|)
  euclid_sentence "2.3.5"
    "And $AE$ is the rectangle contained by $AB$ and $BC$. For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$."
    (step5 : Triangle.area △ a:b:e + Triangle.area △ a:e:f = |(a─b)| * |(b─c)|) := by sorry

  -- @assumption_valid
  have step6_assumption1 : |(d─c)| = |(c─b)| := by euclid_finish
  -- @assumption ("$DC$ (is) equal to $CB$", |(d─c)| = |(c─b)|)
  euclid_sentence "2.3.6"
    "And $AD$ (is) the (rectangle contained) by $AC$ and $CB$. For $DC$ (is) equal to $CB$."
    (step6 : Triangle.area △ a:c:d + Triangle.area △ a:d:f = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.3.7"
    "And $DB$ (is) the square on $CB$."
    (step7 : Triangle.area △ c:b:e + Triangle.area △ c:e:d = |(c─b)| * |(c─b)|) := by sorry

  euclid_sentence "2.3.8"
    "Thus, the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."
    (step8 : |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)|) := by sorry

  exact step8
  euclid_conclude_sentence "2.3.9"
    "Thus, if a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. (Which is) the very thing it was required to show."

end Elements.Book2
