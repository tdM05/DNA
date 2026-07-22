import SystemE

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point)
    (h1 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  euclid_finish

end Elements.Book1
