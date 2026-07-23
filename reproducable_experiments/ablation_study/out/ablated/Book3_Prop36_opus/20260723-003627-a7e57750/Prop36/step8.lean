import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step8 (b d f : Point) (ABC : Circle)
    (h1 : ∠ f:b:d = ∟)
    (h2 : f.isCentre ABC) (h3 : b.onCircle ABC) (h4 : d.outsideCircle ABC) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points f d) as FD
  euclid_apply (proposition_47 b f d FB FD BD)
  euclid_finish

end Elements.Book3
