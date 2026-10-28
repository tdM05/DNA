import SystemE
import Book1.Prop46.Main
import Book1.Prop31.Main
import Book2.Prop03.step1
import Book2.Prop03.step2
import Book2.Prop03.step3
import Book2.Prop03.step4
import Book2.Prop03.step5
import Book2.Prop03.step6
import Book2.Prop03.step7
import Book2.Prop03.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
      |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧ ∠ b:c:d = ∟) := by euclid_apply (helper_2_3_step1 b c d e AB DE CD BE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)))

  -- AF (the parallel through A, step 2.3.3) is what pins F, so it is built here, before F is cut.
  euclid_apply (Elements.Book1.proposition_31 a c d CD) as AF
  euclid_apply (intersection_lines AF DE) as f
  euclid_sentence "2.3.2"
    "and let $ED$ be drawn through to $F$,"
    (step2 : f.onLine DE ∧ between e d f) := by euclid_apply (helper_2_3_step2 a b c d e f AB CD DE BE AF (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)))

  euclid_sentence "2.3.3"
    "and let $AF$ be drawn through $A$, parallel to either of $CD$ or $BE$ [Prop.~1.31]."
    (step3 : a.onLine AF ∧ (¬(AF.intersectsLine CD) ∨ ¬(AF.intersectsLine BE))) := by euclid_apply (helper_2_3_step3 a AF CD BE (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)))

  euclid_sentence "2.3.4"
    "So the (rectangle) $AE$ is equal to the (rectangle) $AD$ and the (square) $CE$."
    (step4 : Triangle.area △ a:b:e + Triangle.area △ a:e:f =
      (Triangle.area △ a:c:d + Triangle.area △ a:d:f) +
      (Triangle.area △ c:b:e + Triangle.area △ c:e:d)) := by euclid_apply (helper_2_3_step4 a b c d e f AB CD DE BE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)))

  -- @assumption_valid
  have step5_assumption1 : |(b─e)| = |(b─c)| := by euclid_finish
  -- @assumption ("$BE$ (is) equal to $BC$", |(b─e)| = |(b─c)|)
  euclid_sentence "2.3.5"
    "And $AE$ is the rectangle contained by $AB$ and $BC$. For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$."
    (step5 : Triangle.area △ a:b:e + Triangle.area △ a:e:f = |(a─b)| * |(b─c)|) := by euclid_apply (helper_2_3_step5 a b c d e f AB CD DE BE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)) (by euclid_assumption "$BE$ (is) equal to $BC$" (show |(b─e)| = |(b─c)|; assumption)))

  -- @assumption_valid
  have step6_assumption1 : |(d─c)| = |(c─b)| := by euclid_finish
  -- @assumption ("$DC$ (is) equal to $CB$", |(d─c)| = |(c─b)|)
  euclid_sentence "2.3.6"
    "And $AD$ (is) the (rectangle contained) by $AC$ and $CB$. For $DC$ (is) equal to $CB$."
    (step6 : Triangle.area △ a:c:d + Triangle.area △ a:d:f = |(a─c)| * |(c─b)|) := by euclid_apply (helper_2_3_step6 a b c d e f AB CD DE AF (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE ∧ between e d f; assumption)) (by euclid_assumption "$DC$ (is) equal to $CB$" (show |(d─c)| = |(c─b)|; assumption)))

  euclid_sentence "2.3.7"
    "And $DB$ (is) the square on $CB$."
    (step7 : Triangle.area △ c:b:e + Triangle.area △ c:e:d = |(c─b)| * |(c─b)|) := by euclid_apply (helper_2_3_step7 b c d e AB DE CD BE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.3.8"
    "Thus, the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."
    (step8 : |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)|) := by euclid_apply (helper_2_3_step8 a b c d e f (by euclid_assumption "" (show Triangle.area △ a:b:e + Triangle.area △ a:e:f = (Triangle.area △ a:c:d + Triangle.area △ a:d:f) + (Triangle.area △ c:b:e + Triangle.area △ c:e:d); assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:e + Triangle.area △ a:e:f = |(a─b)| * |(b─c)|; assumption)) (by euclid_assumption "" (show Triangle.area △ a:c:d + Triangle.area △ a:d:f = |(a─c)| * |(c─b)|; assumption)) (by euclid_assumption "" (show Triangle.area △ c:b:e + Triangle.area △ c:e:d = |(c─b)| * |(c─b)|; assumption)))

  exact step8
  euclid_conclude_sentence "2.3.9"
    "Thus, if a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. (Which is) the very thing it was required to show."

end Elements.Book2
