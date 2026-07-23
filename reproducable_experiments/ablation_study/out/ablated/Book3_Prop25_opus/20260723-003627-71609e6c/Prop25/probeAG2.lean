import SystemE

set_option systemE.solverTime 28

namespace Elements.Book3

-- Probe A: is ∠abd < ∟ derivable from the right triangle ADB (∠adb=∟, d between a c)?
theorem probe_angle (a b c d : Point) (AB DB AC : Line)
    (h8 : d.onLine DB) (h9 : b.onLine DB)
    (h10 : a.onLine AB) (h11 : b.onLine AB)
    (h12 : a.onLine AC) (h13 : c.onLine AC) (h14 : ¬b.onLine AC)
    (h15 : between a d c) (h16 : ∠ a:d:b = ∟)
    (hab : a ≠ b) (hbd : b ≠ d) (hdAB : ¬ d.onLine AB) :
    ∠ a:b:d < ∟ := by
  euclid_finish

-- Probe B: with g.sameSide d AB and ∠abd<∟, does the intersection fire?
theorem probe_int (a b c d g : Point) (AB AG DB AC : Line)
    (h1 : ∠ g:a:b = ∠ a:b:d) (h2 : g ≠ a)
    (h3 : g.sameSide d AB)
    (h4 : a.onLine AG) (h5 : g.onLine AG)
    (h8 : d.onLine DB) (h9 : b.onLine DB)
    (h10 : a.onLine AB) (h11 : b.onLine AB)
    (habd : ∠ a:b:d < ∟) (hab : a ≠ b) (hbd : b ≠ d) :
    AG.intersectsLine DB := by
  euclid_finish

end Elements.Book3
