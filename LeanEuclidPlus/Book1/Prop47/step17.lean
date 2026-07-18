import SystemE
import Mathlib.Tactic.Linarith
import Helpers.Parallel
import Book1.Prop47.step17_ang
import Book1.Prop47.step17_area
import Book1.Prop47.step17_cl
import Book1.Prop47.step17_hc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17
    (a b c d e f g h k l m : Point)
    (AB BC BD BF CE CK DE GF HK AG AH AC AL AE BK : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC) (hmBC : m.onLine BC)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcCK : c.onLine CK) (hkCK : k.onLine CK)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hlDE : l.onLine DE)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAL : a.onLine AL) (hlAL : l.onLine AL) (hmAL : m.onLine AL)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hbBK : b.onLine BK) (hkBK : k.onLine BK)
    (hbac : ∠ b:a:c = ∟) (hbce : ∠ b:c:e = ∟) (hack : ∠ a:c:k = ∟) (hcbd : ∠ c:b:d = ∟)
    (hhaCK : h.sameSide a CK) (hhbAC : ¬h.sameSide b AC) (hdaBC : ¬d.sameSide a BC)
    (hdbCE : d.sameSide b CE)
    (hcag : between c a g) (hbah : between b a h)
    (hALBD : ¬AL.intersectsLine BD) (hAHCK : ¬AH.intersectsLine CK)
    (hHKAC : ¬HK.intersectsLine AC) (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE)
    (hboffAC : ¬b.onLine AC) (haoffBC : ¬a.onLine BC) (hdoffBC : ¬d.onLine BC)
    (hhoffAC : ¬h.onLine AC) (haoffBD : ¬a.onLine BD)
    (hec : e ≠ c) (hkc : k ≠ c) (hbdlen : |(b─d)| = |(b─c)|) (hcelen : |(c─e)| = |(b─c)|)
    (hcklen : |(c─k)| = |(a─c)|)
    (hced : ∠ c:e:d = ∟) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  have hcb : c ≠ b := by euclid_finish
  have hbc : b ≠ c := Ne.symm hcb
  have hce : c ≠ e := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have haoffCE : ¬a.onLine CE := by euclid_finish
  have heoffAC : ¬e.onLine AC := by euclid_finish
  have hle : l ≠ e := by euclid_finish
  have hBCDE : BC ≠ DE := by euclid_finish
  have hAC_ne_BC : AC ≠ BC := by euclid_finish
  have hBC_ne_AB : BC ≠ AB := by euclid_finish
  have hAB_ne_AC : AB ≠ AC := by euclid_finish
  have hALCE : ¬AL.intersectsLine CE := by
    euclid_apply (Elements.not_intersects_trans AL BD CE)
    euclid_finish
  have hCEAL : ¬CE.intersectsLine AL := by euclid_finish
  have hhAB : h.onLine AB := by euclid_finish
  have hAHAB : AH = AB := by euclid_finish
  have hCKAB : ¬CK.intersectsLine AB := by
    rw [hAHAB] at hAHCK; euclid_finish
  have step17_ang : ∠ e:c:a = ∠ k:c:b := by euclid_apply (helper_1_47_step17_ang a b c d e f g h k l AB BC BD BF CE CK DE GF HK AG AH AC AL (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:d = ∟; assumption)) (by euclid_assumption "" (show h.sameSide a CK; assumption)) (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show between c a g; assumption)) (by euclid_assumption "" (show between b a h; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)))
  have step17_area : Triangle.area △ a:c:e = Triangle.area △ k:c:b := by euclid_apply (helper_1_47_step17_area a b c e k AC BC CE AE CK BK AB (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(c─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠ e:c:a = ∠ k:c:b; assumption)))
  have step17_cl : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e := by euclid_apply (helper_1_47_step17_cl a c e l m AC CE BC DE AL AE (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∠ c:e:d = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show ¬e.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show l ≠ e; assumption)) (by euclid_assumption "" (show BC ≠ DE; assumption)))
  have step17_hc : Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ k:c:b + Triangle.area △ k:c:b := by euclid_apply (helper_1_47_step17_hc a b c h k AB BC AC CK HK BK (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show between b a h; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬CK.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  linarith [step17_area, step17_cl, step17_hc]

end Elements.Book1
