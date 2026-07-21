import SystemE

namespace Elements.Book1

theorem helper_1_45_step8 (f g h k m : Point) (FK KH GH : Line)
    (h1 : ∠ h:k:f = ∠ g:h:m)
    (h2 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟)
    (h3 : f.onLine FK) (h4 : k.onLine FK) (h5 : k.onLine KH) (h6 : h.onLine KH)
    (h7 : g.onLine GH) (h8 : h.onLine GH) (h9 : f.sameSide k GH) :
    ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by
  euclid_finish

end Elements.Book1
