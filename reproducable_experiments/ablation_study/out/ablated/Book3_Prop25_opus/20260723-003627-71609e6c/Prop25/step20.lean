import SystemE

namespace Elements.Book3

open Elements.Book1

-- D is the center of the completed circle α₂: it was drawn with center D and radius DA, and
-- since DA = DB = DC, all three points lie on it, so D is indeed its center.
theorem helper_3_25_step20 (a b c d : Point) (α₂ : Circle)
    (h1 : |(d─a)| = |(d─b)|) (h2 : |(d─b)| = |(d─c)|)
    (h3 : d.isCentre α₂) (h4 : a.onCircle α₂) :
    d.isCentre α₂ := by
  euclid_finish

end Elements.Book3
