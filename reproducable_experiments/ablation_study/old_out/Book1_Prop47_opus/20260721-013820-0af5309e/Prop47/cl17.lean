import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

-- parallelogram CL (= C M L E) is double triangle ACE  (Prop 1.41 on base CE, parallels CE ∥ AL)
theorem helper_1_47_cl17 (a c e l m : Point) (AL CE BC DE AC AE : Line)
    (h1 : m.onLine AL) (h2 : l.onLine AL) (h3 : a.onLine AL)
    (h4 : c.onLine CE) (h5 : e.onLine CE) (h6 : c ≠ e)
    (h7 : m.onLine BC) (h8 : c.onLine BC) (h9 : m ≠ c)
    (h10 : l.onLine DE) (h11 : e.onLine DE)
    (h12 : a.onLine AC) (h13 : c.onLine AC) (h14 : a ≠ c)
    (h15 : e.onLine AE) (h16 : a.onLine AE)
    (h17 : ¬(AL.intersectsLine CE)) (h18 : ¬(DE.intersectsLine BC)) (h19 : DE ≠ BC)
    (h20 : ¬(a.onLine CE)) (h21 : ¬(c.onLine AE)) (h22 : ¬(e.onLine AC)) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:c:e + Triangle.area △ a:c:e := by
  have hpara : formParallelogram m l c e AL CE BC DE := by euclid_finish
  have htri : formTriangle a c e AC CE AE := by euclid_finish
  euclid_apply (proposition_41 m c e l a AL CE BC DE AC AE)
  euclid_apply (parallelogram_area m l c e AL CE BC DE)
  euclid_finish

end Elements.Book1
