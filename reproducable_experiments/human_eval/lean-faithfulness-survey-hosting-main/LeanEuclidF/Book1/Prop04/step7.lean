import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_4_s7
  (b c e f : Point) (b' c' : Point) (BC EF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (hassump1 : lineImg BC = EF)
  (h_bc_b'c' : |(b─c)| = |(b'─c')|)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (s1 : ptImg b = e)
  (s3 : ptImg c = f)
  : |(b─c)| = |(e─f)| := by
  have hb'e : b' = e := h_ptImg_b.symm.trans s1
  have hc'f : c' = f := h_ptImg_c.symm.trans s3
  rw [hb'e, hc'f] at h_bc_b'c'
  exact h_bc_b'c'

end Elements.Book1
