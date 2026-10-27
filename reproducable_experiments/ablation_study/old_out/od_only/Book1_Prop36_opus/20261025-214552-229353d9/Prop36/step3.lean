import SystemE

namespace Elements.Book1

theorem helper_1_36_step3 (AH BG : Line)
    (h1 : ¬(AH.intersectsLine BG)) :
    ¬(BG.intersectsLine AH) := by
  euclid_finish

end Elements.Book1
