import SystemE

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF : Line)
    (h1 : ¬(AB.intersectsLine EF)) (h2 : ¬(CD.intersectsLine EF))
    (h3 : AB ≠ CD) (h4 : EF ≠ AB) (h5 : CD ≠ EF)
    (h6 : AB.intersectsLine CD) :
    ¬(AB.intersectsLine CD) := by
  euclid_apply (intersection_lines AB CD) as p
  euclid_finish

end Elements.Book1
