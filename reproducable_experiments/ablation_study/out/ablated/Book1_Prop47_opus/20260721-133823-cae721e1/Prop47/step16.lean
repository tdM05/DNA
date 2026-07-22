import SystemE

namespace Elements.Book1

theorem helper_1_47_step16 (a b c d f g l m : Point)
    (h1 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d)
    (h2 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c)
    (h3 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b := by
  euclid_finish

end Elements.Book1
