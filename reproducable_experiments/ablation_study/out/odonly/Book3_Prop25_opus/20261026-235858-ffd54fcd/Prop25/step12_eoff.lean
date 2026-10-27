import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_eoff (a b c d e : Point) (AC DB AB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hadc : between a d c)
    (hb_off : ¬b.onLine AC) (hb_DB : b.onLine DB)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hstep6a : ∠ b:a:e = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d) :
    ¬ e.onLine AC := by
  -- if e = d then ∠BAE = ∠BAD, but ∠BAE = ∠ABD > ∠BAD, so e ≠ d
  have hed : e ≠ d := by euclid_finish
  -- e is on the perpendicular DB and e ≠ d = AC ∩ DB, so e is off AC
  euclid_finish

end Elements.Book3
