import SystemE

namespace Elements.Book1

theorem helper_1_12_step3 (e g h : Point)
    (h1 : between e h g) (h2 : |(e─h)| = |(h─g)|) :
    between e h g ∧ |(e─h)| = |(h─g)| := by
  euclid_finish

end Elements.Book1
