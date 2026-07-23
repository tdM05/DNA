import SystemE
import Book2.Prop06.Main

namespace Elements.Book3

-- Through-center case: F is the centre on line DA.  |AF| = |FC| (radii, step 4) with A, F, C
-- collinear and A ≠ C makes F the midpoint, hence between A and C.  CD is added straight-on (order
-- A-C-D, i.e. `between d c a`).  Euclid's Prop.~2.6 then gives the rectangle identity.
theorem helper_3_36_step5 (a c d f : Point) (DA : Line)
    (h1 : |(a─f)| = |(f─c)|)
    (ha : a.onLine DA) (hd : d.onLine DA) (hf : f.onLine DA)
    (hdca : between d c a) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  have hc : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hbtw : between a f c := by euclid_finish
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
