import SystemE
import Book1.Prop47.Main

namespace Elements.Book2

open Elements.Book1

-- And the (square) on $AB$ is equal to the (sum of the squares) on $AD$ and $DB$ [Prop.~1.47].
-- Triangle $ADB$ is right-angled at $D$: since $A$ lies between $D$ and $C$, the ray $DA$ coincides
-- with the ray $DC$, so the right-angle $BDC$ at $D$ is also the angle $BDA$.
theorem helper_2_12_step5 (a b c d : Point) (CA AB DB : Line)
    (h1 : d.onLine CA) (h2 : c.onLine CA) (h3 : between d a c)
    (h4 : a.onLine AB) (h5 : b.onLine AB)
    (h6 : b.onLine DB) (h7 : d.onLine DB)
    (h8 : ¬(b.onLine CA))
    (h9 : ∠ b:d:c = ∟) :
    |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB DB)
  euclid_finish

end Elements.Book2
