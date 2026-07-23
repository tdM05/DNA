import SystemE

namespace Elements.Book1

-- between d l e (l = AL ∩ DE), from between b m c and the parallels BD ∥ AL ∥ CE
theorem helper_1_47_dle (b c d e l m : Point) (BC BD CE DE AL : Line)
    (h1 : b.onLine BC) (h2 : c.onLine BC) (h3 : m.onLine BC)
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : c.onLine CE) (h7 : e.onLine CE)
    (h8 : d.onLine DE) (h9 : e.onLine DE) (h10 : l.onLine DE) (hde : d ≠ e)
    (h11 : m.onLine AL) (h12 : l.onLine AL)
    (h13 : ¬(AL.intersectsLine BD)) (h14 : ¬(AL.intersectsLine CE))
    (h15 : ¬(BD.intersectsLine CE))
    (h16 : between b m c)
    (h17 : ¬(d.onLine AL)) (h18 : ¬(e.onLine AL)) (h19 : ¬(l.onLine BD)) (h20 : ¬(l.onLine CE))
    (h21 : d ≠ l) (h22 : e ≠ l) (hbc : b ≠ c) :
    between d l e := by
  euclid_finish

end Elements.Book1
