import SystemE

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF : Line)
    (h1 : AB ≠ CD) (h2 : EF ≠ AB) (h3 : CD ≠ EF)
    (h4 : ¬(AB.intersectsLine EF)) (h5 : ¬(CD.intersectsLine EF)) :
    ¬(AB.intersectsLine CD) := by
  euclid_intros
  euclid_apply (intersection_lines AB CD) as p
  euclid_finish

end Elements.Book1
