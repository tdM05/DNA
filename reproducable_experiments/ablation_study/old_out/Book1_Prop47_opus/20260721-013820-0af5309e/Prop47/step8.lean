import SystemE
import Book1.Prop47.ss1
import Book1.Prop47.ss2
import Book1.Prop47.ss3
import Book1.Prop47.ss4

namespace Elements.Book1

theorem helper_1_47_step8 (a b c d e f g m : Point)
    (AB BC AC BD CE DE BF GF AG AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (hbc : b ≠ c)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : b.onLine BD) (h9 : d.onLine BD) (hbd : b ≠ d)
    (h10 : c.onLine CE) (h11 : e.onLine CE)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : ¬(BD.intersectsLine CE)) (h15 : ¬(DE.intersectsLine BC))
    (h16 : d.sameSide b CE)
    (h17 : b.onLine BF) (h18 : f.onLine BF) (hbf : b ≠ f)
    (h19 : g.onLine GF) (h20 : f.onLine GF)
    (h21 : g.onLine AG) (h22 : a.onLine AG)
    (h23 : ∠ c:b:d = ∟) (h24 : ∠ b:a:c = ∟) (h25 : ∠ a:b:f = ∟) (h26 : ∠ b:a:g = ∟)
    (h27 : ¬(d.onLine BC)) (h28 : ¬(a.onLine BC)) (h29 : ¬(d.sameSide a BC))
    (h30 : ¬(c.onLine AB)) (h31 : ¬(d.onLine AB))
    (h32 : ¬(g.onLine AB)) (h33 : ¬(g.sameSide c AB)) (h34 : g.sameSide a BF)
    (h35 : ¬(BF.intersectsLine AC)) (h36 : ¬(GF.intersectsLine AB))
    (h37 : ¬(a.onLine BF)) (h38 : ¬(c.onLine BF)) (h39 : ¬(f.onLine BC))
    (h40 : a.onLine AL) (h41 : m.onLine AL) (h42 : m.onLine BC)
    (h43 : ¬(AL.intersectsLine BD)) (h44 : ¬(a.onLine BD)) (h45 : ¬(c.onLine BD))
    (h46 : ¬(m.onLine BD))
    (h47 : BD ≠ AB) (h48 : BF ≠ BC)
    (h49 : between b m c) (h50 : between c a g)
    (h51 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) :
    ∠ d:b:a = ∠ f:b:c := by
  euclid_apply (helper_1_47_ss1 a b c d m BC BD AL)
  euclid_apply (helper_1_47_ss2 a b c d e m AB BC AC BD CE DE AL)
  euclid_apply (helper_1_47_ss3 a b c f g AB BC AC BF GF AG)
  euclid_apply (helper_1_47_ss4 a b c f AB BC AC BF)
  euclid_apply (sum_angles_onlyif b d a c BD AB)
  euclid_apply (sum_angles_onlyif b f c a BF BC)
  euclid_finish

end Elements.Book1
