import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_hc_tri
    (b c k : Point) (BK CK BC AB : Line)
    (hbBK : b.onLine BK) (hkBK : k.onLine BK)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hbAB : b.onLine AB)
    (hkoffBC : ¬k.onLine BC) (hboffCK : ¬b.onLine CK) (hkb : k ≠ b) (hcb : c ≠ b) :
    formTriangle b k c BK CK BC := by
  euclid_finish

end Elements.Book1
