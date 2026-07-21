import SystemE

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (KH HM FG GL GH LM : Line)
    (h1 : k.onLine KH) (h2 : h.onLine KH) (h3 : m.onLine HM) (h4 : KH = HM)
    (h5 : f.onLine FG) (h6 : g.onLine FG) (h7 : l.onLine GL) (h8 : FG = GL)
    (h9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h10 : f.sameSide k GH)
    (h11 : l.onLine LM) (h12 : m.onLine LM) (h13 : ¬(GH.intersectsLine LM))
    (h14 : g.onLine GH) (h15 : h.onLine GH) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  euclid_finish

end Elements.Book1
