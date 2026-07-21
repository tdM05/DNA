import SystemE

namespace Elements.Book1

theorem helper_1_36_step9 (a b c d e f g h : Point)
    (hstep7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c)
    (hstep8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h) :
    Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  euclid_finish

end Elements.Book1
