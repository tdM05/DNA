import SystemE
import Book1.Prop47.angleC
import Book1.Prop47.cong17
import Book1.Prop47.cl17
import Book1.Prop47.hc17

namespace Elements.Book1

theorem helper_1_47_step17fin (a b c e h k l m : Point)
    (hcl : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e)
    (hhc : Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ b:c:k + Triangle.area △ b:c:k)
    (hcong : Triangle.area △ c:e:a = Triangle.area △ c:b:k) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  euclid_finish

theorem helper_1_47_step17 (a b c d e h k l m : Point)
    (AB BC AC BD CE DE CK HK AH AL AE BK : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (hbc : b ≠ c)
    (h6 : c.onLine AC) (h7 : a.onLine AC) (hac : a ≠ c)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : c.onLine CE) (h11 : e.onLine CE) (hce : c ≠ e)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : c.onLine CK) (h15 : k.onLine CK) (hck : c ≠ k)
    (h16 : h.onLine HK) (h17 : k.onLine HK) (hhk : h ≠ k)
    (h18 : h.onLine AH) (h19 : a.onLine AH) (h19b : b.onLine AH)
    (h20 : ¬(BD.intersectsLine CE)) (h21 : ¬(DE.intersectsLine BC))
    (h22 : ¬(AL.intersectsLine CE)) (h23 : ¬(CK.intersectsLine AB))
    (h24 : ¬(HK.intersectsLine AC)) (h24b : ¬(AH.intersectsLine CK))
    (h25 : d.sameSide b CE) (h26 : h.sameSide a CK)
    (h27 : ∠ b:c:e = ∟) (h28 : ∠ b:a:c = ∟) (h29 : ∠ a:c:k = ∟) (h30 : ∠ c:a:h = ∟)
    (h31 : ∠ a:m:b = ∟) (h32 : ∠ a:m:c = ∟)
    (h33 : ¬(a.onLine BC)) (h34 : ¬(e.onLine BC)) (h35 : ¬(k.onLine BC))
    (h36 : ¬(a.onLine CE)) (h37 : ¬(b.onLine CE)) (h38 : ¬(m.onLine CE))
    (h39 : ¬(b.onLine AC)) (h40 : ¬(e.onLine AC)) (h41 : ¬(h.onLine AC))
    (h42 : ¬(d.sameSide a BC)) (h43 : ¬(h.sameSide b AC))
    (h44 : ¬(a.onLine CK)) (h45 : ¬(b.onLine CK))
    (h46 : a.onLine AL) (h47 : m.onLine AL) (h48 : m.onLine BC) (h49 : a ≠ m) (h49b : m ≠ c)
    (h50 : CE ≠ AC) (h51 : BC ≠ CK)
    (h52 : between b m c) (h53 : between b a h)
    (h54 : e.onLine AE) (h55 : a.onLine AE)
    (h56 : b.onLine BK) (h57 : k.onLine BK)
    (h58 : CE ≠ AE) (h59 : AE ≠ AC) (h60 : BC ≠ BK) (h61 : BK ≠ CK) (h62 : CK ≠ BC)
    (h63 : |(c─e)| = |(b─c)|) (h64 : |(c─k)| = |(a─c)|)
    (h65 : l.onLine AL) (h66 : l.onLine DE) (h67 : DE ≠ BC)
    (h68 : ¬(c.onLine AE)) (h69 : ¬(a.onLine BK)) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  have hang : ∠ e:c:a = ∠ b:c:k :=
    helper_1_47_angleC a b c d e h k m AB BC AC BD CE DE CK HK AH AL
      h1 h2 h3 h4 h5 hbc h6 h7 hac h8 h9 h10 h11 hce h12 h13 h14 h15 hck h16 h17 h18 h19
      h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41
      h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53
  have hcong : Triangle.area △ c:e:a = Triangle.area △ c:b:k :=
    helper_1_47_cong17 a b c e k CE AE AC BC BK CK
      h10 h11 hce h54 h55 h7 h6 hac h5 h4 hbc.symm h56 h57 h15 h14
      h58 h59 (Ne.symm h50) h60 h61 h62 h63 h64 hang
  have hcl : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e :=
    helper_1_47_cl17 a c e l m AL CE BC DE AC AE
      h47 h65 h46 h10 h11 hce h48 h5 h49b h66 h13 h7 h6 hac h54 h55 h22 h21 h67 h36 h68 h40
  have hhc : Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ b:c:k + Triangle.area △ b:c:k :=
    helper_1_47_hc17 a b c h k AH CK AC HK BC BK
      h19 h18 h19b h14 h15 h7 h6 h16 h17 h4 h5 hbc h56 h57 h24b h24 h44 h35 h41 h69 hhk hac
  exact helper_1_47_step17fin a b c e h k l m hcl hhc hcong

end Elements.Book1
