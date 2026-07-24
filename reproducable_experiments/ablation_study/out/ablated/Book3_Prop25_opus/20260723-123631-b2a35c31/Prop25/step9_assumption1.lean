import SystemE

namespace Elements.Book3

-- The "gap" fact of 3.25.9: angle ABE equals angle BAE.
--   ∠BAE = ∠ABD was constructed (step6): hbae.
--   E lies on DB extended with D between B and E, so rays BE and BD coincide and
--   ∠ABE = ∠ABD.  Hence ∠ABE = ∠ABD = ∠BAE.
theorem helper_3_25_step9_assumption1 (a b d e : Point) (AB DB : Line)
    (hbae : ∠ b:a:e = ∠ a:b:d)
    (hbet : between b d e)
    (hab1 : a.onLine AB) (hab2 : b.onLine AB)
    (hdb1 : d.onLine DB) (hdb2 : b.onLine DB) (hdb3 : e.onLine DB)
    (hab : a ≠ b) (hnaDB : ¬a.onLine DB) :
    ∠ a:b:e = ∠ b:a:e := by
  euclid_finish

end Elements.Book3
