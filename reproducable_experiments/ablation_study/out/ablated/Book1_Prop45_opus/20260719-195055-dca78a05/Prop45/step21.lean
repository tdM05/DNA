import SystemE

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d e₁ e₂ e₃ f g h k l m : Point) (FG KH FK LM GH GL HM : Line)
    (h1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (h2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    (h3 : formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d))
    (h4 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c))
    (h5 : formParallelogram f l k m FG KH FK LM)
    (h6 : f.onLine FG) (h7 : g.onLine FG) (h8 : l.onLine GL) (h9 : FG = GL)
    (h10 : k.onLine KH) (h11 : h.onLine KH) (h12 : m.onLine HM) (h13 : KH = HM)
    (h14 : g.onLine GH) (h15 : h.onLine GH) (h16 : ¬(m.sameSide k GH)) :
    Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_finish

end Elements.Book1
