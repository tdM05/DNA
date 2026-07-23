import SystemE

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC : Circle)
    (h1 : g.insideCircle ABC) (h2 : f ≠ g) (h3 : ¬ between f g a) :
    ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points f g) as L
  euclid_apply (intersection_circle_line_extending_points ABC L g f) as p
  use p
  euclid_finish

end Elements.Book3
