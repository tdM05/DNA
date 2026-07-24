import SystemE
import Book2.Prop06.Main

namespace Elements.Book3

-- the (rectangle contained) by AD and DC plus the (square) on FC is equal to the (square)
-- on FD [Prop.~2.6]. AC is cut in half at F (the centre), and CD is added straight-on.
-- Prop 2.6 with the substitution (a,b,c,d) := (a,c,f,d) on line DA.
theorem helper_3_36_step5 (a c d f : Point) (ABC : Circle) (DA : Line)
    (h1 : f.isCentre ABC) (h2 : a.onCircle ABC) (h3 : c.onCircle ABC)
    (h4 : a.onLine DA) (h5 : d.onLine DA) (h6 : f.onLine DA)
    (h7 : between d c a) (h8 : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
