import SystemE

namespace Elements.Book1

theorem helper_1_47_step2 (a : Point) (AL BD CE : Line)
    (h1 : a.onLine AL) (h2 : ¬(AL.intersectsLine BD)) :
    a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE)) := by
  euclid_finish

end Elements.Book1
