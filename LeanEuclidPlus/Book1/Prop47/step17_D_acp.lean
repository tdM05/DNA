import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_D_acp
    (a c k p : Point) (CK AC : Line)
    (hcCK : c.onLine CK) (hkCK : k.onLine CK) (hpCK : p.onLine CK)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hack : ∠ a:c:k = ∟)
    (hpc : p ≠ c) (hkc : k ≠ c) (hac : a ≠ c) :
    ∠ a:c:p = ∟ := by
  by_cases h : between p c k
  · euclid_finish
  · euclid_apply (equal_angles c p k a a CK AC)
    euclid_finish

end Elements.Book1
