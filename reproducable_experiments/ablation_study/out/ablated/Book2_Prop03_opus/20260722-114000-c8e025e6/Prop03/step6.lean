import SystemE
import Book1Variants.Prop46
import Book1Variants.Prop34
import Book1.Prop30.Main
import Book1.Prop31.Main

namespace Elements.Book2
open Elements.Book1

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (hab : a ≠ b) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hacb : between a c b)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hcAB : c.onLine AB)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (heb : e ≠ b)
    (hdc_be : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hde : |(d─e)| = |(c─b)|) (hcd : |(c─d)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|)
    (haF : a.onLine AF) (hAFCD : ¬(AF.intersectsLine CD))
    (hfAF : f.onLine AF) (hfDE : f.onLine DE)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  have hedf : between e d f := by euclid_finish
  euclid_apply (rectangle_area a c f d AB DE AF CD)
  euclid_apply (proposition_34' a c f d AB DE AF CD)
  euclid_finish

end Elements.Book2
