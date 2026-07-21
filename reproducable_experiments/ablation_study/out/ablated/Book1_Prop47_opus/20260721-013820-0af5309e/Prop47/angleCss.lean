import SystemE
import Book1.Prop47.ss1c
import Book1.Prop47.ss2c
import Book1.Prop47.ss3c
import Book1.Prop47.ss4c

namespace Elements.Book1

theorem angleCss (a b c d e h k m : Point)
    (AB BC AC BD CE DE CK HK AH AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (hbc : b ≠ c)
    (h6 : c.onLine AC) (h7 : a.onLine AC) (hac : a ≠ c)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : c.onLine CE) (h11 : e.onLine CE) (hce : c ≠ e)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : c.onLine CK) (h15 : k.onLine CK) (hck : c ≠ k)
    (h16 : h.onLine HK) (h17 : k.onLine HK)
    (h18 : h.onLine AH) (h19 : a.onLine AH)
    (h20 : ¬(BD.intersectsLine CE)) (h21 : ¬(DE.intersectsLine BC))
    (h22 : ¬(AL.intersectsLine CE)) (h23 : ¬(CK.intersectsLine AB))
    (h24 : ¬(HK.intersectsLine AC))
    (h25 : d.sameSide b CE) (h26 : h.sameSide a CK)
    (h27 : ∠ b:c:e = ∟) (h28 : ∠ b:a:c = ∟) (h29 : ∠ a:c:k = ∟) (h30 : ∠ c:a:h = ∟)
    (h31 : ∠ a:m:b = ∟) (h32 : ∠ a:m:c = ∟)
    (h33 : ¬(a.onLine BC)) (h34 : ¬(e.onLine BC)) (h35 : ¬(k.onLine BC))
    (h36 : ¬(a.onLine CE)) (h37 : ¬(b.onLine CE)) (h38 : ¬(m.onLine CE))
    (h39 : ¬(b.onLine AC)) (h40 : ¬(e.onLine AC)) (h41 : ¬(h.onLine AC))
    (h42 : ¬(d.sameSide a BC)) (h43 : ¬(h.sameSide b AC))
    (h44 : ¬(a.onLine CK)) (h45 : ¬(b.onLine CK))
    (h46 : a.onLine AL) (h47 : m.onLine AL) (h48 : m.onLine BC) (h49 : a ≠ m)
    (h50 : CE ≠ AC) (h51 : BC ≠ CK)
    (h52 : between b m c) (h53 : between b a h) :
    a.sameSide b CE := by
  euclid_apply (helper_1_47_ss1c a b c e m BC CE AL)
  assumption

end Elements.Book1
