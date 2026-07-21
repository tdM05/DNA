import SystemE

namespace Elements.Book1

theorem helper_1_45_step20 (f g h k l m : Point) (FG GL KH HM FK LM GH : Line)
    (h1 : f.onLine FG) (h2 : l.onLine GL) (h3 : FG = GL)
    (h4 : k.onLine KH) (h5 : m.onLine HM) (h6 : KH = HM)
    (h7 : f.onLine FK) (h8 : k.onLine FK)
    (h9 : l.onLine LM) (h10 : m.onLine LM) (h11 : m ≠ l)
    (h12 : ¬(FG.intersectsLine KH))
    (h13 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h14 : f.sameSide k GH)
    (h15 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h16 : ¬(GH.intersectsLine LM)) (h17 : g.onLine GH) (h18 : h.onLine GH) :
    formParallelogram f l k m FG KH FK LM := by
  euclid_finish

end Elements.Book1
