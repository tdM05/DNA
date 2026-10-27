import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7 (b c d e : Point) (AB CD DE BE : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcde : ∠ c:d:e = ∟)
    (hdscBE : d.sameSide c BE)
    (hcd_cb : |(c─d)| = |(c─b)|)
    (hDEAB : ¬DE.intersectsLine AB)
    (hCDBE : ¬CD.intersectsLine BE)
    (heb : e ≠ b) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  have hpara7 : formParallelogram c b d e AB DE CD BE := by euclid_finish
  euclid_apply (rectangle_area c b d e AB DE CD BE)
  have hcb_bc : |(c─b)| = |(b─c)| := by euclid_finish
  have hrect7 : Triangle.area △ c:d:e + Triangle.area △ c:b:e = |(c─b)| * |(c─d)| := by euclid_finish
  have harea7 : Triangle.area △ c:e:b = Triangle.area △ c:b:e := by euclid_finish
  rw [harea7, hrect7, hcd_cb, hcb_bc]

end Elements.Book2
