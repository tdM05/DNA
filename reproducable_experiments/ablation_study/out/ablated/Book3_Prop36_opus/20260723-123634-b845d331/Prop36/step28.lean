import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

-- the (sum of the squares) on EB and BD is equal to the (square) on ED [Prop.~1.47]:
-- triangle EBD is right-angled at B (∠ e:b:d = ∟, step16), so EB² + BD² = ED².
theorem helper_3_36_step28 (b d e : Point) (ABC : Circle)
    (h1 : ∠ e:b:d = ∟) (h2 : e.isCentre ABC) (h3 : b.onCircle ABC)
    (h4 : ¬ d.insideCircle ABC) (h5 : ¬ d.onCircle ABC) :
    |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e d) as ED
  euclid_apply (line_from_points b d) as BD0
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED BD0)
  euclid_finish

end Elements.Book3
