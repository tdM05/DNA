import SystemE

namespace Elements.Book3

-- The two contact points coincide: were d ≠ b, the two distinct common points would force the circles
-- to intersect (step4_int), contradicting ¬intersect.
set_option systemE.solverTime 30 in
theorem helper_3_13_hpb (ABDC EBFD : Circle) (d b g h : Point)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hne : ABDC ≠ EBFD) (hnint : ¬ABDC.intersectsCircle EBFD)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD) :
    d = b := by
  by_contra hdb
  have hgh : g ≠ h := by
    intro heq
    subst heq
    exact hne (by euclid_finish)
  euclid_apply (line_from_points g h) as GH
  have step4_int : ABDC.intersectsCircle EBFD := by sorry
  exact hnint step4_int

end Elements.Book3
