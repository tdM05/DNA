import SystemE

namespace Elements.Book1

theorem helper_1_47_step19 (b c d e : Point) (DE BC BD CE : Line)
    (h1 : d.onLine DE) (h2 : e.onLine DE)
    (h3 : b.onLine BC) (h4 : c.onLine BC)
    (h5 : d.onLine BD) (h6 : b.onLine BD)
    (h7 : e.onLine CE) (h8 : c.onLine CE)
    (h9 : e ≠ c) (h10 : d.sameSide b CE)
    (h11 : ¬(DE.intersectsLine BC)) (h12 : ¬(BD.intersectsLine CE))
    (h13 : ∠ c:b:d = ∟)
    (h14 : |(b─d)| = |(b─c)|) (h15 : |(d─e)| = |(b─c)|) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by
  euclid_apply (rectangle_area d e b c DE BC BD CE)
  euclid_finish

end Elements.Book1
