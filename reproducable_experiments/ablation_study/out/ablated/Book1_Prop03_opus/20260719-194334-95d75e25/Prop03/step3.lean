import SystemE

theorem helper_1_3_step3 (a d e : Point) (DEF : Circle)
    (h1 : a.isCentre DEF) (h2 : d.onCircle DEF) (h3 : e.onCircle DEF) :
    |(a─e)| = |(a─d)| := by
  euclid_finish
