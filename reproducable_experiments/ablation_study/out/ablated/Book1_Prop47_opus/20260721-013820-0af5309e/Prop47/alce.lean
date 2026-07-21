import SystemE

namespace Elements.Book1

-- AL ∥ CE : both parallel to BD; if they met at p, parallel_line_unique forces AL = CE ∋ a, contra.
theorem helper_1_47_alce (a b c d e : Point) (AL BD CE : Line)
    (h1 : a.onLine AL) (h2 : ¬(AL.intersectsLine BD)) (h3 : ¬(a.onLine BD))
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : ¬(BD.intersectsLine CE)) (h7 : c.onLine CE) (h8 : e.onLine CE)
    (h9 : ¬(a.onLine CE)) :
    ¬(AL.intersectsLine CE) := by
  by_contra hcon
  euclid_apply (intersection_lines AL CE) as p
  euclid_apply (parallel_line_unique p BD AL CE)
  euclid_finish

end Elements.Book1
