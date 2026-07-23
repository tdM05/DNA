import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- $EBD$ is a right-angle (III.18, the tangent $DB$ meets radius $EB$ at right-angles), so
-- Pythagoras (Prop.~1.47) on triangle $EBD$ gives the square on $ED$ as the sum of the squares on
-- $EB$ and $BD$.
theorem helper_3_36_step28 (b d e : Point) (ABC : Circle)
    (h1 : ∠ e:b:d = ∟)
    (h2 : e.isCentre ABC) (h3 : b.onCircle ABC) (h4 : d.outsideCircle ABC) :
    |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points e d) as ED
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED BD)
  euclid_finish

end Elements.Book3
