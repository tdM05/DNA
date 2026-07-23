import SystemE
import Book1.Prop04.Main

namespace Elements.Book1

-- △ CEA ≅ △ CBK (SAS: CE=CB, CA=CK, ∠ECA=∠BCK) ⟹ equal area
theorem helper_1_47_cong17 (a b c e k : Point) (CE AE AC BC BK CK : Line)
    (h1 : c.onLine CE) (h2 : e.onLine CE) (h3 : c ≠ e)
    (h4 : e.onLine AE) (h5 : a.onLine AE)
    (h6 : a.onLine AC) (h7 : c.onLine AC) (h8 : a ≠ c)
    (h9 : c.onLine BC) (h10 : b.onLine BC) (h11 : c ≠ b)
    (h12 : b.onLine BK) (h13 : k.onLine BK)
    (h14 : k.onLine CK) (h15 : c.onLine CK)
    (h16 : CE ≠ AE) (h17 : AE ≠ AC) (h18 : AC ≠ CE)
    (h19 : BC ≠ BK) (h20 : BK ≠ CK) (h21 : CK ≠ BC)
    (h22 : |(c─e)| = |(b─c)|) (h23 : |(c─k)| = |(a─c)|)
    (h24 : ∠ e:c:a = ∠ b:c:k) :
    Triangle.area △ c:e:a = Triangle.area △ c:b:k := by
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_finish

end Elements.Book1
