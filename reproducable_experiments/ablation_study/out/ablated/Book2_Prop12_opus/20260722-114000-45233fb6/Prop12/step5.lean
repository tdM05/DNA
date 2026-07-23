import SystemE
import Book1.Prop47.Main

set_option systemE.solverTime 120

namespace Elements.Book2

open Elements.Book1

theorem helper_2_12_step5 (a b c d : Point) (AB CA : Line)
    (h1 : d.onLine CA) (h3 : a.onLine CA)
    (h6 : a.onLine AB) (h7 : b.onLine AB) (h8 : a ≠ b)
    (h9 : CA ≠ AB)
    (h11 : between d a c) (h12 : ∠ b:d:c = ∟) :
    |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points b d) as BD
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB BD)
  first | assumption | euclid_finish

end Elements.Book2
