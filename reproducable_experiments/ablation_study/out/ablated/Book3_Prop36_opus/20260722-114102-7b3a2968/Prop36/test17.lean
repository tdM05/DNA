import SystemE
import Book3.Prop03.Main

set_option systemE.solverTime 45

namespace Elements.Book3

-- Test J: Pythagorean EQUATION + f≠a ⟹ leg < hypotenuse
theorem test17_J (a e f : Point)
    (hpyth : |(e─a)| * |(e─a)| = |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)|)
    (hne : f ≠ a) :
    |(e─f)| < |(e─a)| := by
  euclid_finish

-- Test K: Pythagorean EQUATION + f≠a + centre + on-circle ⟹ inside
theorem test17_K (a e f : Point) (ABC : Circle)
    (he : e.isCentre ABC) (h2 : a.onCircle ABC)
    (hpyth : |(e─a)| * |(e─a)| = |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)|)
    (hne : f ≠ a) :
    f.insideCircle ABC := by
  euclid_finish

end Elements.Book3
