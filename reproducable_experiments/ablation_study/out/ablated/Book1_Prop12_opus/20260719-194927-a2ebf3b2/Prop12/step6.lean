import SystemE

namespace Elements.Book1

theorem helper_1_12_step6 (c e g h : Point)
    (h1 : |(g─h)| = |(h─e)|) (h2 : |(h─c)| = |(h─c)|) :
    |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)| := by
  euclid_finish

end Elements.Book1
