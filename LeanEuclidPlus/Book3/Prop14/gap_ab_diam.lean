import SystemE
import Mathlib.Tactic.Linarith

namespace Elements.Book3

-- @euclid_gap: e = f means the foot on AB is the centre, i.e. AB is a diameter.
-- Euclid reads "AB is not a diameter" off the figure and draws the perpendicular EF.
-- With the (faithful) hypotheses `between a f b` / `between c g d` — exactly what the
-- cited III.3 needs and what the perpendicular-foot construction provides — the
-- proposition IS true and provable in this branch (equal chords ⟹ CD is a diameter
-- too, so g = e).  Without those hypotheses the foot-at-endpoint model (c = g on a
-- diameter) is a genuine counterexample; see STATUS.md.
set_option systemE.solverTime 30 in
theorem helper_3_14_gap_ab_diam
    (a b c d e f g : Point) (ABDC : Circle) (AB CD : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab_ne : a ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd_ne : c ≠ d)
    (hfAB : f.onLine AB) (hfangle : ∠ a:f:e = ∟) (hafb : between a f b)
    (hgCD : g.onLine CD) (hgangle : ∠ c:g:e = ∟) (hcgd : between c g d)
    (h_ef : e = f) :
    (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
    (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by
  have heonAB : e.onLine AB := h_ef ▸ hfAB
  have hbet_aeb : between a e b := by rw [h_ef]; exact hafb
  constructor
  · -- Direction 1: |AB| = |CD| ⟹ |EF| = |EG| (both are 0: e = f and e = g).
    intro h_ab_cd
    have hef0 : |(e─f)| = 0 := zero_segment_onlyif e f h_ef
    have hdiam_ab : |(a─b)| = |(a─e)| + |(a─e)| := by sorry
    have hpyth_c : |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)| := by sorry
    have hpyth_d : |(d─g)| * |(d─g)| + |(g─e)| * |(g─e)| = |(a─e)| * |(a─e)| := by sorry
    have hchord_cd : |(c─g)| + |(g─d)| = |(c─d)| := between_if c g d hcgd
    have hge0 : |(g─e)| = 0 := by sorry
    have heg0 : |(e─g)| = 0 := by rw [segment_symmetric e g]; exact hge0
    rw [hef0, heg0]
  · -- Direction 2: |EF| = |EG| ⟹ |AB| = |CD|.  |EF| = 0 forces e = g (CD diameter).
    intro h_efeg
    have hef0 : |(e─f)| = 0 := zero_segment_onlyif e f h_ef
    have heg0 : |(e─g)| = 0 := by linarith
    have h_eg : e = g := zero_segment_if e g heg0
    have hbet_ced : between c e d := by rw [h_eg]; exact hcgd
    have hdiam_ab : |(a─b)| = |(a─e)| + |(a─e)| := by sorry
    have hdiam_cd : |(c─d)| = |(a─e)| + |(a─e)| := by sorry
    linarith

end Elements.Book3
