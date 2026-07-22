import SystemE

namespace Elements.Book1

theorem helper_1_47_step7 (a b c d f : Point)
    (h1 : ∠ d:b:c = ∠ f:b:a) (h2 : (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟)) :
    ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c := by
  euclid_finish

end Elements.Book1
