import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step20_gb
    (a b f g : Point) (GF AB AG BF : Line)
    (hgpar : formParallelogram g f a b GF AB AG BF)
    (hgAG : g.onLine AG) (haAG : a.onLine AG) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbag : ∠ b:a:g = ∟)
    (hgflen : |(g─f)| = |(a─b)|) (haglen : |(a─g)| = |(a─b)|) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)| := by
  euclid_apply (rectangle_area g f a b GF AB AG BF)
  have hgoal : Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(g─f)| * |(g─a)| := by euclid_finish
  have hga : |(g─a)| = |(a─b)| := by euclid_finish
  have hba : |(b─a)| = |(a─b)| := by euclid_finish
  rw [hgoal, hgflen, hga, hba]

end Elements.Book1
