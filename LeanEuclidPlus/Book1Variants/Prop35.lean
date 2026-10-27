import SystemE

namespace Elements.Book1

theorem proposition_35' : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC →
  Triangle.area △a:b:d  + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f := by
  sorry

end Elements.Book1
