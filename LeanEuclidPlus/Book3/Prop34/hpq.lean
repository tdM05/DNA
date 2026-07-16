import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_34_hpq (b : Point) (EF : Line) (hb_EF : b.onLine EF) :
    ∃ p q : Point, p.onLine EF ∧ q.onLine EF ∧ between p b q := by
  obtain ⟨p, hbp, hp_EF⟩ := exists_distincts_points_on_line EF b
  euclid_apply (extend_point EF p b) as q
  exact ⟨p, q, hp_EF, by euclid_finish, by euclid_finish⟩

end Elements.Book3
