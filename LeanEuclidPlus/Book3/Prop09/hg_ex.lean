import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_9_hg_ex
    (ABC : Circle) (d e : Point) (GK : Line)
    (hd_inside : d.insideCircle ABC)
    (hd_GK : d.onLine GK)
    (he_GK : e.onLine GK)
    (hed : e ≠ d)
    : ∃ g : Point, g.onCircle ABC ∧ g.onLine GK := by
  obtain ⟨g, hg_circle, hg_GK, _⟩ :=
    intersection_circle_line_extending_points ABC GK d e ⟨hd_inside, ⟨hd_GK, he_GK, hed.symm⟩⟩
  exact ⟨g, hg_circle, hg_GK⟩

end Elements.Book3
