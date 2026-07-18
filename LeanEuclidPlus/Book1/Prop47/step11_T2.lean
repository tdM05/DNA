import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step11_T2
    (b c f : Point) (BC FC BF : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hfoffBC : ¬f.onLine BC) (hboffFC : ¬b.onLine FC) (hfb : f ≠ b) (hcf : c ≠ f) :
    formTriangle b c f BC FC BF := by
  euclid_finish

end Elements.Book1
