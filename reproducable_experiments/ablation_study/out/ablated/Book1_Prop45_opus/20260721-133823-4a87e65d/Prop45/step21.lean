import SystemE

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (FG KH FK LM : Line)
    (h1 : formParallelogram f l k m FG KH FK LM)
    (h2 : between f g l) (h3 : between k h m)
    (h4 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (h5 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :
    Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
