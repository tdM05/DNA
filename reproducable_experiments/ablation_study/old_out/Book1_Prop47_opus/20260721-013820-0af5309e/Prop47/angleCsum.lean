import SystemE

namespace Elements.Book1

theorem helper_1_47_angleCsum (a b c e k : Point) (BC AC CE CK : Line)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (hbc : b ≠ c)
    (h6 : c.onLine AC) (h7 : a.onLine AC) (hac : a ≠ c)
    (h10 : c.onLine CE) (h11 : e.onLine CE) (hce : c ≠ e)
    (h14 : c.onLine CK) (h15 : k.onLine CK) (hck : c ≠ k)
    (h27 : ∠ b:c:e = ∟) (h29 : ∠ a:c:k = ∟)
    (h33 : ¬(a.onLine BC)) (h39 : ¬(b.onLine AC))
    (h37 : ¬(b.onLine CE)) (h44 : ¬(a.onLine CK))
    (h50 : CE ≠ AC) (h51 : BC ≠ CK)
    (s1 : a.sameSide b CE) (s2 : e.sameSide b AC)
    (s3 : k.sameSide a BC) (s4 : b.sameSide a CK) :
    ∠ e:c:a = ∠ b:c:k := by
  euclid_apply (sum_angles_onlyif c e a b CE AC)
  euclid_apply (sum_angles_onlyif c b k a BC CK)
  euclid_finish

end Elements.Book1
