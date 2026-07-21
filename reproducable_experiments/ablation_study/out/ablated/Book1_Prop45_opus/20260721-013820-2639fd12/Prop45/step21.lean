import SystemE

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (KH HM FG GL GH LM : Line)
    (h1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (h2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    (h3 : KH = HM) (h4 : FG = GL)
    (h5 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (h6 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h7 : k.onLine KH) (h8 : h.onLine KH) (h9 : m.onLine HM)
    (h10 : f.onLine FG) (h11 : g.onLine FG) (h12 : l.onLine GL)
    (h13 : g.onLine GH) (h14 : h.onLine GH)
    (h15 : f.sameSide k GH)
    (h16 : l.onLine LM) (h17 : m.onLine LM) (h18 : ¬(GH.intersectsLine LM)) :
    Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_finish

end Elements.Book1
