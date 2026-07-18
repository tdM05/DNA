import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step20_hc
    (a c h k : Point) (HK AC AH CK : Line)
    (hhpar : formParallelogram h k a c HK AC AH CK)
    (hhAH : h.onLine AH) (haAH : a.onLine AH) (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcah : ∠ c:a:h = ∟)
    (hhklen : |(h─k)| = |(a─c)|) (hahlen : |(a─h)| = |(a─c)|) :
    Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)| := by
  euclid_apply (rectangle_area h k a c HK AC AH CK)
  have hgoal : Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(h─k)| * |(h─a)| := by euclid_finish
  have hha : |(h─a)| = |(a─c)| := by euclid_finish
  rw [hgoal, hhklen, hha]

end Elements.Book1
