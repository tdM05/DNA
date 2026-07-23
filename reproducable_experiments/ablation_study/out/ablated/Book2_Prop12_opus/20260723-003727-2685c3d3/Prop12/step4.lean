import SystemE
import Book1.Prop47.Main

namespace Elements.Book2

open Elements.Book1

-- The (square) on $CB$ is equal to the (sum of the squares) on $CD$ and $DB$, since the angle at
-- $D$ is a right-angle [Prop.~1.47]. Triangle $CDB$ is right-angled at $D$.
theorem helper_2_12_step4 (a b c d : Point) (CA BC DB : Line)
    (h1 : d.onLine CA) (h2 : c.onLine CA) (h3 : between d a c)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : b.onLine DB) (h7 : d.onLine DB)
    (h8 : ¬(b.onLine CA))
    (h9 : ∠ b:d:c = ∟) :
    |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (Elements.Book1.proposition_47 d c b CA BC DB)
  euclid_finish

end Elements.Book2
