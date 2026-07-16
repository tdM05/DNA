import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_23_hfoff (c d e a b f g : Point) (AB : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hg_AB : g.onLine AB)
    (h_af : |(a─f)| = |(c─d)|) (h_ag : |(a─g)| = |(c─e)|) (h_fg : |(f─g)| = |(e─d)|)
    (h1 : |(d─c)| + |(c─e)| > |(d─e)|)
    (h2 : |(e─d)| + |(d─c)| > |(e─c)|)
    (h3 : |(c─e)| + |(e─d)| > |(c─d)|)
    : ¬f.onLine AB := by
  euclid_finish

end Elements.Book1
