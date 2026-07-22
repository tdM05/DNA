import SystemE

namespace Elements.Book1

theorem helper_1_45_step8 (f g h k m : Point)
    (h1 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m)
    (h2 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟) :
    ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by
  euclid_finish

end Elements.Book1
