import SystemE

namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) := by
  euclid_intros
  euclid_intro_sentence "1.43.0"
    "For any parallelogram, the complements of the parallelograms about the diagonal are equal to one another. Let $ABCD$ be a parallelogram, and $AC$ its diagonal. And let $EH$ and $FG$ be the parallelograms about  $AC$, and $BK$ and $KD$ the so-called complements (about $AC$). I say that the complement $BK$ is equal to the complement $KD$. "

  -- @assumption_valid
  have step1_assumption1 : formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$ABCD$ is a parallelogram, and $AC$ its diagonal", formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC)
  euclid_sentence "1.43.1"
    "For since $ABCD$ is a parallelogram, and $AC$ its diagonal,  triangle $ABC$ is equal to triangle $ACD$ [Prop.~1.34]."
    (step1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d) := by sorry

  -- @assumption_valid
  have step2_assumption1 : formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC := by euclid_finish
  -- @assumption ("$EH$ is a parallelogram, and $AK$ is its diagonal", formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC)
  euclid_sentence "1.43.2"
    "Again, since $EH$ is a parallelogram, and $AK$ is its diagonal, triangle $AEK$ is equal to triangle $AHK$ [Prop.~1.34]."
    (step2 : Triangle.area △ a:e:k = Triangle.area △ a:h:k) := by sorry

  euclid_sentence "1.43.3"
    "So, for the same (reasons), triangle $KFC$ is also equal to (triangle) $KGC$."
    (step3 : Triangle.area △ k:f:c = Triangle.area △ k:g:c) := by sorry

  -- @assumption_valid
  have step4_assumption1 : Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c := by euclid_finish
  -- @assumption ("triangle $AEK$ is equal to triangle $AHK$, and $KFC$ to $KGC$", Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c)
  euclid_sentence "1.43.4"
    "Therefore, since triangle $AEK$ is equal to triangle $AHK$, and $KFC$ to $KGC$, triangle $AEK$ plus $KGC$ is equal to triangle $AHK$ plus $KFC$."
    (step4 : Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c) := by sorry

  euclid_sentence "1.43.5"
    "And the whole triangle $ABC$ is also equal to the whole (triangle) $ADC$."
    (step5 : Triangle.area △ a:b:c = Triangle.area △ a:d:c) := by sorry

  euclid_sentence "1.43.6"
    "Thus, the remaining complement $BK$ is equal to the remaining complement $KD$. "
    (step6 : Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) := by sorry

  exact step6
  euclid_conclude_sentence "1.43.7"
    "Thus, for any parallelogramic figure, the complements of the parallelograms about the diagonal are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
