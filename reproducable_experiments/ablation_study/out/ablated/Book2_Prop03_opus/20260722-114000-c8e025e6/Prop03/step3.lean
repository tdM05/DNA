import SystemE

namespace Elements.Book2

theorem helper_2_3_step3 (a : Point) (CD AF : Line)
    (haF : a.onLine AF) (hAFCD : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  exact ⟨haF, hAFCD⟩

end Elements.Book2
