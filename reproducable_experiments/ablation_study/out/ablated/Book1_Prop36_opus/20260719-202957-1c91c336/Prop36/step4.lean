import SystemE

namespace Elements.Book1

theorem helper_1_36_step4 (b c e h : Point) (BE CH : Line)
    (h1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH)
    (p27 : b.onLine BE) (p28 : e.onLine BE) (p29 : c.onLine CH) (p30 : h.onLine CH) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
