import SystemE

set_option systemE.solverTime 300
set_option maxHeartbeats 0

namespace Elements.Book2

-- $AD$ is the rectangle contained by $AC$ and $CB$, since $DC = CB$.  Apply `rectangle_area` at
-- corner $C$: parallelogram (c a d f) with side C-A on AB, adjacent side C-D on CD, opposite side
-- D-F on DE, remaining side A-F on AF.  The right angle is ∠ C:D:F = ∟ (supplement of the square
-- corner ∠ C:D:E along the straight line E-D-F).  Its area (△ A:C:D + △ A:F:D) equals
-- |C─A| · |C─D| = |A─C| · |C─B|.
theorem helper_2_3_step6 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (h1 : e.onLine DE) (h2 : d.onLine DE)
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : c.onLine AB)
    (h6 : a.onLine AF) (h7 : f.onLine AF)
    (h9 : e.onLine BE) (h10 : b.onLine BE) (h11 : e ≠ b)
    (h12 : d.onLine CD) (h13 : c.onLine CD)
    (h14 : ¬(AF.intersectsLine CD)) (h15 : ¬(CD.intersectsLine BE))
    (h16 : ¬(DE.intersectsLine AB))
    (h17 : between a c b)
    (h18 : |(d─e)| = |(c─b)|) (h19 : |(b─e)| = |(c─b)|)
    (h20 : ∠ b:c:d = ∟) (h21 : ∠ c:d:e = ∟)
    (hs2 : f.onLine DE ∧ between e d f)
    (step6_assumption1 : |(c─d)| = |(c─b)|) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  have hcdf : ∠ c:d:f = ∟ := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  euclid_apply (rectangle_area c a d f AB DE CD AF)
  euclid_finish

end Elements.Book2
