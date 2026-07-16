import SystemE
import Book1.Prop06.Main


namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_hEb (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (hbet : between a d c) (hb_off : ¬b.onLine AC)
    (hd_db : d.onLine DB) (hb_db : b.onLine DB) (he_db : e.onLine DB)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (ha_ag3 : a.onLine AG3) (hg3_ag3 : g3.onLine AG3) (he_ag3 : e.onLine AG3) (hg3_ne : g3 ≠ a)
    (hside : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hright : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─b)| := by
  have hEb_ang : ∠ a:b:e = ∠ b:a:e := by sorry
  have hEb_tri : formTriangle e a b AG3 AB DB := by sorry
  euclid_apply (proposition_6 e a b AG3 AB DB)
  euclid_finish

end Elements.Book3
