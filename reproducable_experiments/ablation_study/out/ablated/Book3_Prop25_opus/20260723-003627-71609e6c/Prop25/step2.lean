import SystemE
import Book1.Prop11.Main

namespace Elements.Book3

open Elements.Book1

-- DB is drawn from the midpoint D at right angles to AC [Prop.~1.11]. Because b is
-- equidistant from a and c (|ab|=|cb|) and d is the midpoint (|ad|=|dc|), triangles ADB
-- and CDB are congruent (SSS), so ∠ADB = ∠CDB; with d between a and c these are right angles.
theorem helper_3_25_step2 (a b c d : Point) (AC : Line)
    (h1 : a.onLine AC) (h2 : c.onLine AC) (h3 : ¬b.onLine AC)
    (h4 : between a d c) (h5 : |(a─d)| = |(d─c)|) (h6 : |(a─b)| = |(c─b)|) :
    ∠ a:d:b = ∟ := by
  euclid_apply (proposition_11 a c d AC) as f
  euclid_finish

end Elements.Book3
