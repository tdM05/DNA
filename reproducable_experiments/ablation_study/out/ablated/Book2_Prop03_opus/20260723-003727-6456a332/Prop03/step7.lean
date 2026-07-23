import SystemE

set_option systemE.solverTime 300

namespace Elements.Book2

-- `DB` is the square on `CB`.  Its area (split along the diagonal `CE`) is `△ c:d:e + △ c:e:b`.
-- The square is the parallelogram `d e c b` (top `DE`, base `AB`, sides `CD`, `BE`), with the
-- right angle at `C` (`∠ d:c:b`, which is the square's `∠ b:c:d`).  `rectangle_area` gives the
-- diagonal split as `|(d─e)| * |(d─c)|`, and `|(d─e)| = |(c─d)| = |(c─b)|`, hence `|(c─b)|²`.
theorem helper_2_3_step7 (a b c d e : Point) (AB DE CD BE : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB)
    (h4 : d.onLine DE) (h5 : e.onLine DE)
    (h6 : c.onLine CD) (h7 : d.onLine CD)
    (h8 : b.onLine BE) (h9 : e.onLine BE)
    (h10 : between a c b)
    (h11 : ¬(DE.intersectsLine AB)) (h12 : ¬(CD.intersectsLine BE))
    (h13 : d.sameSide c BE)
    (h14 : ∠ b:c:d = ∟)
    (h15 : |(d─e)| = |(c─b)|) (h16 : |(c─d)| = |(c─b)|) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  euclid_assert (∠ d:c:b = ∟)
  euclid_apply (parallelogram_same_side d e c b DE AB CD BE)
  euclid_assert (formParallelogram d e c b DE AB CD BE)
  euclid_apply (rectangle_area d e c b DE AB CD BE)
  euclid_finish

end Elements.Book2
