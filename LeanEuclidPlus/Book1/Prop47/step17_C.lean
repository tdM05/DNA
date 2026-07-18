import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_C
    (a b c k : Point) (CK AC BC : Line)
    (hcCK : c.onLine CK) (hkCK : k.onLine CK)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hbaCK : b.sameSide a CK) (hkbAC : ¬k.sameSide b AC)
    (hboffAC : ¬b.onLine AC) (hkc : k ≠ c) :
    k.sameSide a BC := by
  euclid_apply (triple_incidence_2 CK AC BC c k a b)
  euclid_finish

end Elements.Book1
