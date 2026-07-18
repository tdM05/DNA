import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_area_T2
    (b c k : Point) (BC BK CK : Line)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hbBK : b.onLine BK) (hkBK : k.onLine BK)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK)
    (hkoffBC : ¬k.onLine BC) (hboffCK : ¬b.onLine CK) (hkb : k ≠ b) (hcb : c ≠ b) :
    formTriangle c b k BC BK CK := by
  euclid_finish

end Elements.Book1
