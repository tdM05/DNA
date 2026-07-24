import SystemE
import Book1.Prop04.Main

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12 (a b c d e g : Point) (AC AB DB AG EC : Line)
    (hsad : |(a─d)| = |(c─d)|) (hde : |(d─e)| = |(d─e)|)
    (hang : ∠ a:d:e = ∠ c:d:e)
    (hac1 : a.onLine AC) (hac2 : c.onLine AC) (hbet : between a d c)
    (hag1 : a.onLine AG) (hag2 : e.onLine AG)
    (hdb1 : d.onLine DB) (hdb3 : e.onLine DB)
    (hec1 : e.onLine EC) (hec2 : c.onLine EC)
    (hbAC : ¬b.onLine AC) (hac : a ≠ c) (hea : e ≠ a) (hce : e ≠ c) :
    |(a─e)| = |(c─e)| := by
  euclid_apply (proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3
