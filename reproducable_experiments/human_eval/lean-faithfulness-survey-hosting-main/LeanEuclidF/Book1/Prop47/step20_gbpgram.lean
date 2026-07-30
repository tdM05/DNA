import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s20_x1
    (a b g f : Point) (AB GF AG BF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (h_g_same_a_BF : g.sameSide a BF)
    (h_nGFAB : ¬GF.intersectsLine AB) (h_nAGBF : ¬AG.intersectsLine BF) :
    formParallelogram a b g f AB GF AG BF := by
  euclid_finish

end Elements.Book1
