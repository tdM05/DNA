import SystemE

namespace Elements.Book2

theorem helper_2_3_step8 (a b c d e f : Point)
    (s4 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b))
    (s5 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|)
    (s6 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|)
    (s7 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  euclid_finish

end Elements.Book2
