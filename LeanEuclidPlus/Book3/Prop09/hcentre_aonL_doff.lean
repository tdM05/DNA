import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop08.Main

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_9_hcentre_aonL_doff
    (ABC α₀ : Circle)
    (a b d e o : Point)
    (AB L : Line)
    (ha : a.onCircle ABC)
    (hb : b.onCircle ABC)
    (h_da_db : |(d─a)| = |(d─b)|)
    (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB)
    (haeb : between a e b)
    (hae_eb : |(a─e)| = |(e─b)|)
    (ho : o.isCentre ABC)
    (hdo : ¬d = o)
    (hda : d ≠ a)
    (hd_ctr : d.isCentre α₀)
    (ha_α₀ : a.onCircle α₀) (hb_α₀ : b.onCircle α₀) (hc_α₀ : c.onCircle α₀)
    (hαABC : ¬α₀ = ABC)
    (hd_L : d.onLine L) (ho_L : o.onLine L)
    (h_ab : ¬a.sameSide b L) (h_ac : ¬a.sameSide c L) (h_bc : ¬b.sameSide c L)
    (haL : a.onLine L)
    : ¬(d.onLine AB) → False := by
  intro hdAB
  have hed : e ≠ d := by euclid_finish
  obtain ⟨ED, he_ED, hd_ED⟩ := line_from_points e d hed
  have he_AB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
  -- Sub-node 1: ∠a:e:d = ∟ (SSS proof in hcentre_perp_d.lean)
  have hcentre_perp_d : ∠ a:e:d = ∟ := by sorry
  -- Case split: o on AB?
  by_cases hoAB : o.onLine AB
  · -- Case: o on AB → L = AB → d on AB → contradiction
    have hoa : a ≠ o := by euclid_finish
    have hLAB : L = AB :=
      two_points_determine_line a o L AB ⟨⟨haL, ho_L, hoa⟩, ha_AB, hoAB⟩
    exact hdAB (hLAB ▸ hd_L)
  · -- Sub-node 2: ∠a:e:o = ∟ (SSS proof in hcentre_perp_o.lean)
    have hcentre_perp_o : ∠ a:e:o = ∟ := by sorry
    -- Derive ∠d:e:b = ∟ and ∠o:e:b = ∟
    have hd_eb : ∠ d:e:b = ∟ := by
      have := perpendicular_onlyif a b e d AB ⟨ha_AB, hb_AB, haeb, hdAB, hcentre_perp_d⟩
      linarith
    have hoe : o ≠ e := by euclid_finish
    have ho_eb : ∠ o:e:b = ∟ := by
      have := perpendicular_onlyif a b e o AB ⟨ha_AB, hb_AB, haeb, hoAB, hcentre_perp_o⟩
      linarith
    have hflat : ∠ a:e:b = ∟ + ∟ := flat_angle_onlyif a e b haeb
    -- Sub-node 3: o on line ED (hcentre_oED.lean)
    have hcentre_oED : o.onLine ED := by sorry
    -- ED = L (d and o both on both)
    have hEDL : ED = L :=
      two_points_determine_line d o ED L ⟨⟨hd_ED, hcentre_oED, hdo⟩, hd_L, ho_L⟩
    -- e on L, then L = AB, contradiction
    have he_L : e.onLine L := hEDL ▸ he_ED
    have hae : a ≠ e := by euclid_finish
    have hLAB : L = AB :=
      two_points_determine_line a e L AB ⟨⟨haL, he_L, hae⟩, ha_AB, he_AB⟩
    exact hdAB (hLAB ▸ hd_L)

end Elements.Book3
