import SystemE
import Book1Variants.Prop46
import Book1Variants.Prop34
import Book1.Prop30.Main
import Book1.Prop31.Main

namespace Elements.Book2
open Elements.Book1

theorem helper_2_3_step7 (a b c d e : Point) (AB CD DE BE : Line)
    (hab : a ≠ b) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hacb : between a c b)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hcAB : c.onLine AB)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (heb : e ≠ b)
    (hdc_be : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hde : |(d─e)| = |(c─b)|) (hcd : |(c─d)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  euclid_apply (rectangle_area d e c b DE AB CD BE)
  euclid_finish

end Elements.Book2
