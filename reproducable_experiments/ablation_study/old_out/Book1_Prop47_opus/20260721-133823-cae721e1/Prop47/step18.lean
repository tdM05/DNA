import SystemE

namespace Elements.Book1

theorem helper_1_47_step18 (a b c d e f g h k l m : Point)
    (h1 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (h2 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c)
    (h3 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ b:m:l + Triangle.area △ b:l:d) +
      (Triangle.area △ c:e:l + Triangle.area △ c:l:m)) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  euclid_finish

end Elements.Book1
