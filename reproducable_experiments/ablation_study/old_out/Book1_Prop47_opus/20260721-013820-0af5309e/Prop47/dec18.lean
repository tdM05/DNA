import SystemE

namespace Elements.Book1

-- square BDEC = parallelogram BL + parallelogram CL  (split by ML)
theorem helper_1_47_dec18 (b c d e l m : Point) (AL BC BD CE DE : Line)
    (h1 : d.onLine DE) (h2 : e.onLine DE) (h3 : l.onLine DE)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : m.onLine BC)
    (h7 : d.onLine BD) (h8 : b.onLine BD)
    (h9 : e.onLine CE) (h10 : c.onLine CE) (hec : e ≠ c)
    (h11 : m.onLine AL) (h12 : l.onLine AL)
    (h13 : ¬(DE.intersectsLine BC)) (h14 : ¬(BD.intersectsLine CE))
    (h15 : ¬(AL.intersectsLine BD)) (h16 : d.sameSide b CE) (h17 : m.sameSide b DE)
    (h18 : between b m c) (h19 : between d l e) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ b:m:l + Triangle.area △ b:l:d) +
      (Triangle.area △ c:e:l + Triangle.area △ c:l:m) := by
  have hp1 : formParallelogram d e b c DE BC BD CE := by euclid_finish
  have hp2 : formParallelogram m l b d AL BD BC DE := by euclid_finish
  euclid_apply (sum_parallelograms_area d e b c l m DE BC BD CE)
  euclid_apply (parallelogram_area d e b c DE BC BD CE)
  euclid_apply (parallelogram_area m l b d AL BD BC DE)
  euclid_finish

end Elements.Book1
