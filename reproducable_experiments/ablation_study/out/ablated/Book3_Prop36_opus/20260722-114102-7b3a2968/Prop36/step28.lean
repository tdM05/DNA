import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

theorem helper_3_36_step28 (b d e : Point) (ABC : Circle) (EB ED DB : Line)
    (h1 : ∠ e:b:d = ∟) (h2 : e.isCentre ABC) (h3 : b.onCircle ABC) (h4 : ¬ d.onCircle ABC)
    (h5 : e.onLine EB) (h6 : b.onLine EB)
    (h7 : e.onLine ED) (h8 : d.onLine ED)
    (h9 : b.onLine DB) (h10 : d.onLine DB) :
    |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB)
  euclid_finish

end Elements.Book3
