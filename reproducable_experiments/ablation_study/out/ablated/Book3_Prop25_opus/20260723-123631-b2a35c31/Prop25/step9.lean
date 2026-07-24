import SystemE
import Book1.Prop06.Main

namespace Elements.Book3

open Elements.Book1

-- Triangle E A B has equal base angles ∠ABE = ∠BAE, so the opposite sides EA, EB are equal [Prop.~1.6].
theorem helper_3_25_step9 (a b c d e g : Point) (AC AB DB AG : Line)
    (hang : ∠ a:b:e = ∠ b:a:e)
    (hab1 : a.onLine AB) (hab2 : b.onLine AB)
    (hag1 : a.onLine AG) (hag2 : e.onLine AG)
    (hdb1 : d.onLine DB) (hdb2 : b.onLine DB) (hdb3 : e.onLine DB)
    (hac1 : a.onLine AC) (hac2 : c.onLine AC) (hbet : between a d c)
    (hbAC : ¬b.onLine AC) (hac : a ≠ c) :
    |(e─b)| = |(e─a)| := by
  euclid_apply (proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3
