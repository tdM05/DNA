import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step14_tri
    (b c f : Point) (FC BF BC AC : Line)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hfBF : f.onLine BF) (hbBF : b.onLine BF)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC) (hcAC : c.onLine AC)
    (hBFAC : ¬BF.intersectsLine AC) (hboffAC : ¬b.onLine AC) (hbc : b ≠ c) (hfb : f ≠ b) :
    formTriangle c f b FC BF BC := by
  have hcb : c ≠ b := Ne.symm hbc
  have hBFAC_ne : BF ≠ AC := fun h => hboffAC (h ▸ hbBF)
  have hBFBC : BF ≠ BC := by
    intro h; rw [← h] at hcBC
    euclid_apply (intersection_lines_common_point c BF AC)
    euclid_finish
  have hfoffBC : ¬f.onLine BC := by euclid_finish
  have hcoffBF : ¬c.onLine BF := by euclid_finish
  have hcf : c ≠ f := by euclid_finish
  euclid_finish

end Elements.Book1
