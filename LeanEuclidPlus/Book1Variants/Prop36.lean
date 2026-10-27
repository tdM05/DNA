import SystemE

namespace Elements.Book1

theorem proposition_36' : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line) ,
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  sorry

end Elements.Book1
