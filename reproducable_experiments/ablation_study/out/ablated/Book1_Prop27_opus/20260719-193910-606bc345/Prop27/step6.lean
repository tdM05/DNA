import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_27_step6 (a d e f b g : Point) (AE FD EF : Line)
    (hae1 : a.onLine AE) (hae2 : e.onLine AE) (hae3 : a ≠ e)
    (hfd1 : f.onLine FD) (hfd2 : d.onLine FD) (hfd3 : f ≠ d)
    (hef1 : e.onLine EF) (hef2 : f.onLine EF) (hef3 : e ≠ f)
    (hop1 : ¬a.onLine EF) (hop2 : ¬d.onLine EF) (hop3 : ¬(a.sameSide d EF))
    (hang : ∠ a:e:f = ∠ e:f:d)
    (hint : AE.intersectsLine FD)
    (hb1 : b.onLine AE) (hb2 : between a e b)
    (hg1 : g.onLine AE) (hg2 : g.onLine FD) :
    ¬(g.opposingSides b EF) := by
  intro hac
  obtain ⟨hac1, hac2, hac3⟩ := hac
  -- `a` and `b` lie on opposite sides of `EF` (`e` between them, `e ∈ EF`).
  have h_ab : a.opposingSides b EF := by euclid_finish
  -- `a` opposite `b`, `a` opposite `d`  ⟹  `b` and `d` on the same side.
  have h_bd : b.sameSide d EF := by euclid_finish
  -- `g` opposite `b`, `b` same as `d`  ⟹  `g` and `d` on opposite sides.
  have h_gd : g.opposingSides d EF := by euclid_finish
  -- `g` and `d` on `FD`, on opposite sides of `EF` crossing at `f`  ⟹  `f` between them.
  have h_gfd : between g f d := by euclid_finish
  -- `g` lies on the same side of `e` (along `AE`) as `a`, so the ray `e→g` is the ray `e→a`.
  have h_rayE : ∠ g:e:f = ∠ a:e:f := by euclid_finish
  -- Prop.~1.16 on triangle EGF: exterior ∠EFD exceeds the interior opposite ∠GEF.
  euclid_apply (proposition_16 e g f d AE FD EF)
  euclid_finish

end Elements.Book1
