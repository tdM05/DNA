import SystemE
import Book2.Prop06.Main

namespace Elements.Book3

theorem helper_3_36_step20 (a c d e f : Point) (ABC : Circle) (DA : Line)
    (h1 : a.onCircle ABC) (h2 : c.onCircle ABC) (h3 : e.isCentre ABC)
    (h4 : a.onLine DA) (h5 : d.onLine DA) (h6 : f.onLine DA)
    (h7 : between d c a) (h8 : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
