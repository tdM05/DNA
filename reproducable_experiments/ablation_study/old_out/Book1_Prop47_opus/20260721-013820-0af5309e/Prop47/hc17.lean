import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

-- square HC (= A C K H) is double triangle BCK  (Prop 1.41 on base CK, parallels CK ∥ AB=AH)
theorem helper_1_47_hc17 (a b c h k : Point) (AH CK AC HK BC BK : Line)
    (h1 : a.onLine AH) (h2 : h.onLine AH) (h3 : b.onLine AH)
    (h4 : c.onLine CK) (h5 : k.onLine CK)
    (h6 : a.onLine AC) (h7 : c.onLine AC)
    (h8 : h.onLine HK) (h9 : k.onLine HK)
    (h10 : b.onLine BC) (h11 : c.onLine BC) (h12 : b ≠ c)
    (h13 : b.onLine BK) (h14 : k.onLine BK)
    (h15 : ¬(AH.intersectsLine CK)) (h16 : ¬(HK.intersectsLine AC))
    (h17 : ¬(a.onLine CK)) (h18 : ¬(k.onLine BC)) (h19 : ¬(h.onLine AC))
    (h20 : ¬(a.onLine BK)) (h21 : h ≠ k) (h22 : a ≠ c) :
    Triangle.area △ a:h:k + Triangle.area △ a:k:c = Triangle.area △ b:c:k + Triangle.area △ b:c:k := by
  have hpara : formParallelogram a h c k AH CK AC HK := by euclid_finish
  have htri : formTriangle b c k BC CK BK := by euclid_finish
  euclid_apply (proposition_41 a c k h b AH CK AC HK BC BK)
  euclid_apply (parallelogram_area a h c k AH CK AC HK)
  euclid_finish

end Elements.Book1
