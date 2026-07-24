import SystemE

set_option systemE.solverTime 300
set_option maxHeartbeats 0

namespace Elements.Book2

-- $DB$ is the square on $CB$.  Apply `rectangle_area` to the square C D E B taken at corner $C$:
-- parallelogram (c b d e) with side C-B on AB, adjacent side C-D on CD, opposite side D-E on DE,
-- remaining side B-E on BE.  The right angle is ∠ C:D:E = ∟ (a square corner).  Its area
-- (△ C:D:E + △ C:B:E) equals |C─B| · |C─D| = |B─C| · |B─C| since |C─D| = |C─B|.
theorem helper_2_3_step7 (b c d e : Point) (AB DE CD BE : Line)
    (h1 : c.onLine AB) (h2 : b.onLine AB)
    (h3 : d.onLine DE) (h4 : e.onLine DE)
    (h5 : c.onLine CD) (h6 : d.onLine CD)
    (h7 : b.onLine BE) (h8 : e.onLine BE) (h9 : e ≠ b)
    (h10 : ¬(DE.intersectsLine AB)) (h11 : ¬(CD.intersectsLine BE))
    (h12 : d.sameSide c BE)
    (h13 : |(c─d)| = |(c─b)|) (h14 : ∠ c:d:e = ∟) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  euclid_apply (rectangle_area c b d e AB DE CD BE)
  euclid_finish

end Elements.Book2
