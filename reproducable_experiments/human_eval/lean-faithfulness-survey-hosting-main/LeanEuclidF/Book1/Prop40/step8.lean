import SystemE
import Book1.Prop39.Main
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_40_s8
    (a b c d e f : Point) (BC AF CD AD DE FE : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfCD : f.onLine CD) (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hnAF : ¬AF.intersectsLine BC)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hade : a ≠ d)
    (hcon : AD.intersectsLine BC)
    (hCDBC : CD ≠ BC) (hBCDE : BC ≠ DE) (hDECD : DE ≠ CD)
    (hdcne : d ≠ c) (hbene : b ≠ e)
    (hassume1 : |(b─c)| = |(c─e)|)
    (haside : a.sameSide d BC)
    (hstep7 : Triangle.area △ d:c:e = Triangle.area △ f:c:e) :
    False := by

  have hdf : d ≠ f := by
    intro hdf
    have hdAF : d.onLine AF := hdf ▸ hfAF
    have hAFAD : AF = AD :=
      two_points_determine_line a d AF AD ⟨⟨haAF, hdAF, hade⟩, haAD, hdAD⟩
    exact hnAF (hAFAD ▸ hcon)

  have hanotBC : ¬a.onLine BC := same_side_not_on_line a d BC haside

  have hafBC : a.sameSide f BC :=
    sameSide_of_parallel' a f a AF BC haAF hfAF haAF hanotBC hnAF

  have hdfBC : d.sameSide f BC := by euclid_finish

  have hformDCE : formTriangle d c e CD BC DE :=
    ⟨⟨hdCD, hcCD, hdcne⟩, hcBC, heBC, heDE, hdDE, hCDBC, hBCDE, hDECD⟩

  have hformFCE : formTriangle f c e CD BC FE := by euclid_finish

  have hdfCD : distinctPointsOnLine d f CD := ⟨hdCD, hfCD, hdf⟩

  have hnotCDBC : ¬CD.intersectsLine BC :=
    proposition_39 d c e f CD BC DE CD FE CD
      ⟨hformDCE, hformFCE, hdfBC, hstep7, hdfCD⟩

  exact hnotCDBC (intersection_lines_common_point c CD BC ⟨hcCD, hcBC, hCDBC⟩)

end Elements.Book1
