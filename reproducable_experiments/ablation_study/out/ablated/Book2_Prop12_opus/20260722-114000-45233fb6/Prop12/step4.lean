import SystemE
import Book1.Prop47.Main

set_option systemE.solverTime 120

namespace Elements.Book2

open Elements.Book1

theorem helper_2_12_step4 (a b c d : Point) (BC CA : Line)
    (h1 : d.onLine CA) (h2 : c.onLine CA)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h10 : BC ≠ CA)
    (h11 : between d a c) (h12 : ∠ b:d:c = ∟) :
    |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points b d) as BD
  euclid_apply (Elements.Book1.proposition_47 d c b CA BC BD)
  first | assumption | euclid_finish

end Elements.Book2
