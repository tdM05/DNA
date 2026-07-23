import SystemE

namespace Elements.Book3

theorem helper_3_6_step3 (b e f : Point) (ABC CDE : Circle) (FEB : Line)
    (h1 : b.onCircle ABC) (h2 : e.onCircle CDE) (h3 : f.onLine FEB)
    (h4 : e.onLine FEB) (h5 : b.onLine FEB) :
    b.onCircle ABC ∧ e.onCircle CDE ∧
    f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB := by
  euclid_finish

end Elements.Book3
