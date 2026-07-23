import SystemE
import Book1.Prop20.Main

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point) (ABC : Circle)
    (ha1 : |(f─a)| = |(f─h)|)
    (ha2 : |(a─g)| + |(g─f)| > |(f─h)|)
    (hb1 : a.onCircle ABC) (hb2 : f.isCentre ABC) (hb3 : h.onCircle ABC)
    (hb4 : between f g h) (hb5 : h ≠ a) (hb6 : |(g─a)| < |(f─a)|) :
    |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f g) as FG
  euclid_apply (line_from_points a g) as GA
  euclid_apply (proposition_20 a f g AF FG GA)
  euclid_finish

end Elements.Book3
