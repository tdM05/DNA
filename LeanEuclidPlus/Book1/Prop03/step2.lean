import SystemE

namespace Elements.Book1

theorem helper_1_3_step2 (a d : Point) (DEF : Circle)
  (h1 : a.isCentre DEF)
  (h2 : d.onCircle DEF) :
  a.isCentre DEF ∧ d.onCircle DEF := by
  euclid_finish

end Elements.Book1
