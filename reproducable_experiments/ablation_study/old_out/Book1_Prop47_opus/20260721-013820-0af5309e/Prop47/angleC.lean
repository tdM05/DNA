import SystemE
import Book1.Prop47.ss1c
import Book1.Prop47.ss2c
import Book1.Prop47.ss3c
import Book1.Prop47.ss4c
import Book1.Prop47.angleCsum

namespace Elements.Book1

-- ∠ e:c:a = ∠ b:c:k  (mirror of step8's angle addition, at vertex c)
theorem helper_1_47_angleC (a b c d e h k m : Point)
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
    ∠ e:c:a = ∠ b:c:k := by
  have s1 : a.sameSide b CE :=
    helper_1_47_ss1c a b c e m BC CE AL h46 h47 h22 h48 h4 h5 h10 h11 h52 h36 h37 h38
  have s2 : e.sameSide b AC :=
    helper_1_47_ss2c a b c d e m AB BC AC BD CE DE AL h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h20 h21 h25 h27 h28 h34 h33 h42 h39 h40 h46 h47 h48 h22 h52
  have s3 : k.sameSide a BC :=
    helper_1_47_ss3c a b c h k AB BC AC CK HK AH h1 h2 h3 h4 h5 h6 h7 h14 h15 h16 h17 h18 h19 h29 h30 h28 h41 h39 h43 h26 h23 h24 h53 h33 h35
  have s4 : b.sameSide a CK :=
    helper_1_47_ss4c a b c k AB BC AC CK h1 h2 h3 h4 h5 h6 h7 h14 h15 h29 h28 h23 h44 h45
  exact helper_1_47_angleCsum a b c e k BC AC CE CK h4 h5 hbc h6 h7 hac h10 h11 hce h14 h15 hck h27 h29 h33 h39 h37 h44 h50 h51 s1 s2 s3 s4

end Elements.Book1
