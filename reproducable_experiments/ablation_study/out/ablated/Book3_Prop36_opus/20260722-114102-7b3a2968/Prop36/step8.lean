import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

theorem helper_3_36_step8 (b d f : Point) (ABC : Circle) (FB DB : Line)
    (h1 : ∠ f:b:d = ∟) (h2 : f.isCentre ABC) (h3 : b.onCircle ABC)
    (h4 : ¬ d.insideCircle ABC) (h5 : ¬ d.onCircle ABC)
    (h6 : f.onLine FB) (h7 : b.onLine FB) (h8 : b.onLine DB) (h9 : d.onLine DB) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points f d) as FD
  euclid_apply (Elements.Book1.proposition_47 b f d FB FD DB)
  euclid_finish

end Elements.Book3
