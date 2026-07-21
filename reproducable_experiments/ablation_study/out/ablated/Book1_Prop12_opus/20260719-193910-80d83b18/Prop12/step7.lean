import SystemE

namespace Elements.Book1

theorem helper_1_12_step7 (c e g : Point) (EFG : Circle)
    (h1 : c.isCentre EFG) (h2 : e.onCircle EFG) (h3 : g.onCircle EFG) :
    |(c─g)| = |(c─e)| := by
  euclid_finish

end Elements.Book1
