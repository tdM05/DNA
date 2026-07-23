import SystemE

set_option systemE.solverTime 300

namespace Elements.Book2

-- Combining: `AE = AD + CE` (step4), and the three pieces are the named rectangles/square
-- (steps 5,6,7).  Substituting gives `AB·BC = AC·CB + BC·BC`.
theorem helper_2_3_step8 (a b c d e f : Point)
    (h1 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b))
    (h2 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|)
    (h3 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|)
    (h4 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  euclid_finish

end Elements.Book2
