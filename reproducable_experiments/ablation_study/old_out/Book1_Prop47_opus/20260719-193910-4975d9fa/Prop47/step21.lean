import SystemE

namespace Elements.Book1

theorem helper_1_47_step21 (a b c d e f g h k : Point)
    (h18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c))
    (h19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|)
    (h20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_finish

end Elements.Book1
