import SystemE
import Book1.Prop04.Main
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step17 (a b c e h k l m : Point)
    (AL CE DE BC AE AC AH CK HK BK : Line)
    (h1 : l.onLine AL) (h2 : m.onLine AL) (h3 : a.onLine AL)
    (h4 : e.onLine CE) (h5 : c.onLine CE)
    (h6 : l.onLine DE) (h7 : e.onLine DE)
    (h8 : m.onLine BC) (h9 : b.onLine BC) (h10 : c.onLine BC)
    (h11 : a.onLine AE) (h12 : e.onLine AE)
    (h13 : a.onLine AC) (h14 : c.onLine AC)
    (h15 : a.onLine AH) (h16 : h.onLine AH) (h17 : b.onLine AH)
    (h18 : c.onLine CK) (h19 : k.onLine CK)
    (h20 : h.onLine HK) (h21 : k.onLine HK)
    (h22 : b.onLine BK) (h23 : k.onLine BK)
    (h24 : ¬(AL.intersectsLine CE)) (h25 : ¬(DE.intersectsLine BC))
    (h26 : ¬(AH.intersectsLine CK))
    (h27 : |(c─e)| = |(b─c)|) (h28 : |(c─k)| = |(a─c)|)
    (h29 : ∠ e:c:a = ∠ b:c:k)
    (h30 : ¬(a.onLine BC)) (h31 : ¬(b.onLine AC))
    (h32 : ∠ b:c:e = ∟) (h33 : ∠ a:c:k = ∟) (h34 : ∠ c:a:h = ∟) (h35 : ∠ b:a:c = ∟) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  euclid_apply (proposition_41 l e c m a AL CE DE BC AE AC)
  euclid_apply (proposition_41 a c k h b AH CK AC HK BC BK)
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_finish

end Elements.Book1
