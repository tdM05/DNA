import SystemE
import Book1.Prop20.Main

namespace Elements.Book3

open Elements.Book1

theorem helper_3_11_step3 (a f g h d : Point) (ABC ADE : Circle)
    (hcentreABC : f.isCentre ABC) (haABC : a.onCircle ABC) (hhABC : h.onCircle ABC)
    (hcentreADE : g.isCentre ADE) (haADE : a.onCircle ADE) (hdADE : d.onCircle ADE)
    (hginside : g.insideCircle ABC) (hnotint : ¬ ABC.intersectsCircle ADE)
    (hfgh : between f g h) (hgdh : between g d h) (hgalt : |(g─a)| < |(f─a)|)
    (hfg : f ≠ g)
    (h1 : |(f─a)| = |(f─h)|)
    (h2 : |(a─g)| + |(g─f)| > |(f─h)|) :
    |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points g f) as GF
  euclid_apply (line_from_points f a) as FA
  euclid_apply (proposition_20 a g f AG GF FA)
  euclid_finish

end Elements.Book3
