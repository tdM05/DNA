import SystemE

namespace Elements.Book1

theorem helper_1_36_step4 (b c e h : Point) (BE CH : Line)
    (h1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  euclid_finish

end Elements.Book1
