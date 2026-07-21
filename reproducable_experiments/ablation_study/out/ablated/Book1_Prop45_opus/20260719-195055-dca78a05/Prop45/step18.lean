import SystemE

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (KH FG HM GL GH LM : Line)
    (h1 : k.onLine KH) (h2 : m.onLine HM) (h3 : KH = HM)
    (h4 : f.onLine FG) (h5 : l.onLine GL) (h6 : FG = GL)
    (h7 : f.sameSide k GH) (h8 : ¬m.onLine GH) (h9 : ¬k.onLine GH) (h10 : ¬(m.sameSide k GH))
    (h11 : m.onLine LM) (h12 : l.onLine LM) (h13 : ¬(GH.intersectsLine LM)) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  euclid_finish

end Elements.Book1
