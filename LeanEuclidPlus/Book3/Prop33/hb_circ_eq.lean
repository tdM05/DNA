import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hb_circ_eq
    (a b f g : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_f_FG : f.onLine FG) (h_g_FG : g.onLine FG)
    (h_afeq : |(a─f)| = |(f─b)|)
    (hafg : ∠ a:f:g = ∟) (hbfg : ∠ b:f:g = ∟) :
    |(a─g)| = |(b─g)| := by
  euclid_finish

end Elements.Book3
