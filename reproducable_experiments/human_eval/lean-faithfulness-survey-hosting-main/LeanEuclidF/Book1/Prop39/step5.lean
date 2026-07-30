import SystemE
import Book1Variants.Prop37
import Book1.Prop39.step5_triEBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s5
    (a b c d e : Point) (AB BC AC BD CD EC AE : Line)

    (haAB : a.onLine AB) (hbAB : b.onLine AB) (habne : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)

    (hdBD : d.onLine BD) (hbBD : b.onLine BD) (hdbne : d ≠ b) (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hBDBC : BD ≠ BC) (hBCCD : BC ≠ CD) (hCDBD : CD ≠ BD)

    (heBD : e.onLine BD) (hcEC : c.onLine EC) (heEC : e.onLine EC)

    (hasdBC : a.sameSide d BC)

    (haAE : a.onLine AE) (heAE : e.onLine AE)

    (hassump1 : ¬(AE.intersectsLine BC))
    : Triangle.area △ a:b:c = Triangle.area △ e:b:c := by
  by_cases hane : a = e
  · subst hane; rfl
  · have s5_x17 : formTriangle e b c BD BC EC := by euclid_apply (h_1_39_s5_x3 a e b c d BD BC EC AE CD (by (show e.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine EC; assumption)) (by (show e.onLine EC; assumption)) (by (show BD ≠ BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show d ≠ b; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show ¬(AE.intersectsLine BC); assumption)) (by (show a.sameSide d BC; assumption)))
    have s5_x12 : distinctPointsOnLine a e AE := ⟨haAE, heAE, hane⟩
    euclid_apply (proposition_37' a b c e AB BC AC BD EC AE)
    euclid_finish

end Elements.Book1
