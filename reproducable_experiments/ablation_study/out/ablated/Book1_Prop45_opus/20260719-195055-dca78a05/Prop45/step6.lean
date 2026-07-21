import SystemE

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FK KH GH : Line)
    (h1 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
    (h2 : f.onLine FK) (h3 : k.onLine FK) (h4 : k.onLine KH) (h5 : h.onLine KH)
    (h6 : g.onLine GH) (h7 : h.onLine GH) (h8 : f.sameSide k GH) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  euclid_finish

end Elements.Book1
