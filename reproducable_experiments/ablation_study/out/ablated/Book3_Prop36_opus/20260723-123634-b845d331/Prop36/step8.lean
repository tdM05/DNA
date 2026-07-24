import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- the (square) on FD is equal to the (sum of the squares) on FB and BD [Prop.~1.47]:
-- triangle FBD is right-angled at B (∠ f:b:d = ∟, step3), so FD² = FB² + BD².
theorem helper_3_36_step8 (b d f : Point) (ABC : Circle)
    (h1 : ∠ f:b:d = ∟) (h2 : f.isCentre ABC) (h3 : b.onCircle ABC)
    (h4 : ¬ d.insideCircle ABC) (h5 : ¬ d.onCircle ABC) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points d b) as DB0
  euclid_apply (Elements.Book1.proposition_47 b f d FB FD DB0)
  euclid_finish

end Elements.Book3
