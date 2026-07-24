import SystemE
import Book1.Prop11.Main

namespace Elements.Book3

open Elements.Book1

-- 3.25.2 : DB is at right-angles to AC at D.  Here b is equidistant from a and c
-- (|ab|=|cb|) and d is the midpoint (|ad|=|dc|), so triangles ADB and CDB are
-- congruent (SSS), whence ∠ADB = ∠CDB; being supplementary (a,d,c collinear) each
-- is a right angle.  Euclid erects the perpendicular by [Prop.~1.11], which we cite.
theorem helper_3_25_step2 (a b c d : Point) (AC DB : Line)
    (h1 : |(a─b)| = |(c─b)|)
    (h2 : |(a─d)| = |(d─c)|)
    (h3 : between a d c)
    (h4 : a.onLine AC)
    (h5 : c.onLine AC)
    (h6 : ¬b.onLine AC)
    (h7 : a ≠ c)
    (h8 : d.onLine DB)
    (h9 : b.onLine DB) :
    ∠ a:d:b = ∟ := by
  euclid_apply (proposition_11 a c d AC) as f
  euclid_finish

end Elements.Book3
