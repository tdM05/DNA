import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop08.Main

namespace Elements.Book3

open Elements.Book1

/-
  hcentre_aonL: False when a.onLine L (line through centers d and o).

  Case d.onLine AB: L = AB → b.onLine L → circle_line_intersections gives
    between a d b and between a o b; metric + betweenness → d = o. Contradiction.
  Case d.off AB: sorry sub-node (requires SSS + perpendicular bisector argument).
-/
set_option systemE.solverTime 30 in
theorem helper_3_9_hcentre_aonL
    (ABC α₀ : Circle)
    (a b c d e f : Point) (o : Point)
    (AB BC L : Line)
    (hd_inside : d.insideCircle ABC)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hc : c.onCircle ABC)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_da_db : |(d─a)| = |(d─b)|) (h_db_dc : |(d─b)| = |(d─c)|)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (haeb : between a e b) (hae_eb : |(a─e)| = |(e─b)|)
    (hbfc : between b f c) (hbf_fc : |(b─f)| = |(f─c)|)
    (ho : o.isCentre ABC)
    (hdo : ¬d = o)
    (hda : d ≠ a)
    (hd_ctr : d.isCentre α₀)
    (ha_α₀ : a.onCircle α₀) (hb_α₀ : b.onCircle α₀) (hc_α₀ : c.onCircle α₀)
    (hαABC : ¬α₀ = ABC)
    (hd_L : d.onLine L) (ho_L : o.onLine L)
    (h_ab : ¬a.sameSide b L) (h_ac : ¬a.sameSide c L) (h_bc : ¬b.sameSide c L)
    (haL : a.onLine L)
    : False := by
  have he_onAB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
  have hd_in_α₀ : d.insideCircle α₀ := center_inside_circle d α₀ hd_ctr
  have ho_in_ABC : o.insideCircle ABC := center_inside_circle o ABC ho
  -- Case split: d on AB (leads to d=o) vs d off AB (sorry sub-node)
  have hcentre_aonL_doff : ¬(d.onLine AB) → False := by sorry
  rcases Classical.em (d.onLine AB) with hdAB | hdAB
  · -- Case 1: d.onLine AB → L = AB → circle_line_intersections → d = o
    have hLAB : L = AB :=
      two_points_determine_line a d L AB ⟨⟨haL, hd_L, hda.symm⟩, ha_AB, hdAB⟩
    have hb_onL : b.onLine L := hLAB ▸ hb_AB
    have hbet_adb : between a d b :=
      circle_line_intersections d a b L α₀ ⟨hd_L, haL, hb_onL, hd_in_α₀, ha_α₀, hb_α₀, hab⟩
    have hbet_aob : between a o b :=
      circle_line_intersections o a b L ABC ⟨ho_L, haL, hb_onL, ho_in_ABC, ha, hb, hab⟩
    -- metric: both d and o are midpoints of ab → d = o
    have hbetd := between_if a d b hbet_adb
    have hbeto := between_if a o b hbet_aob
    have hoa_ob : |(o─a)| = |(o─b)| := by linarith [point_on_circle_onlyif o a b ABC ⟨ho, ha, hb⟩]
    have hdo' : d = o := by euclid_finish
    exact hdo hdo'
  · exact hcentre_aonL_doff hdAB

end Elements.Book3
