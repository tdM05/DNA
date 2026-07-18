import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_D_abp
    (a b f p : Point) (BF AB : Line)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hpBF : p.onLine BF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (habf : ∠ a:b:f = ∟)
    (hpb : p ≠ b) (hfb : f ≠ b) (hab : a ≠ b) :
    ∠ a:b:p = ∟ := by
  by_cases h : between p b f
  · euclid_finish
  · euclid_apply (equal_angles b p f a a BF AB)
    euclid_finish

end Elements.Book1
