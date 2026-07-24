import SystemE

namespace Elements.Book2

theorem helper_2_3_step3 (a : Point) (AF CD : Line)
    (h1 : a.onLine AF) (h2 : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  euclid_finish

end Elements.Book2
