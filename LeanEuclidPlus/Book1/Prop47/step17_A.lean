import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_A
    (a b c e : Point) (CE BC AC : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (habCE : a.sameSide b CE) (headBC : ¬e.sameSide a BC)
    (haoffBC : ¬a.onLine BC) (hec : e ≠ c) :
    e.sameSide b AC := by
  euclid_apply (triple_incidence_2 CE BC AC c e b a)
  euclid_finish

end Elements.Book1
