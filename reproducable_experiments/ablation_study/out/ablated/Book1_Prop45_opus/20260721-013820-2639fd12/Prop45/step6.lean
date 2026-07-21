import SystemE

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FG KH FK GH : Line)
    (h1 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
    (h2 : f.onLine FG) (h3 : g.onLine FG) (h4 : k.onLine KH) (h5 : h.onLine KH)
    (h6 : f.onLine FK) (h7 : k.onLine FK) (h8 : g.onLine GH) (h9 : h.onLine GH) (h10 : g ≠ h)
    (h11 : f.sameSide k GH) (h12 : ¬(FG.intersectsLine KH)) (h13 : ¬(FK.intersectsLine GH)) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  euclid_finish

end Elements.Book1
