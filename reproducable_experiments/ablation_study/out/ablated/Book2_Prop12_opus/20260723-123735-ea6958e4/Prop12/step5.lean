import SystemE
import Book1.Prop47.Main

namespace Elements.Book2

-- The (square) on $AB$ is equal to the (sum of squares) on $AD$ and $DB$
-- [Prop.~1.47] (right triangle $ADB$, right-angle at $D$).
theorem helper_2_12_step5 (a b c d : Point) (AB BC CA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_CA : c.onLine CA) (ha_CA : a.onLine CA) (hd_CA : d.onLine CA)
    (hAB_BC : AB ≠ BC) (hBC_CA : BC ≠ CA) (hCA_AB : CA ≠ AB)
    (hbet : between d a c)
    (h1 : ∠ b:d:c = ∟) :
    |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points b d) as BD
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB BD)
  euclid_finish

end Elements.Book2
