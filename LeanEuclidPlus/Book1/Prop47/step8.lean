import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop47.step8_ahBF
import Book1.Prop47.step8_ahBD
import Book1.Prop47.step8_ahBC
import Book1.Prop47.step8_agBC
import Book1.Prop47.step8_gfAB
import Book1.Prop47.step8_ecBD
import Book1.Prop47.step8_bcAL
import Book1.Prop47.step8_dle
import Book1.Prop47.step8_B
import Book1.Prop47.step8_A
import Book1.Prop47.step8_D
import Book1.Prop47.step8_C
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8
    (a b c d e f g h l : Point) (AB BC BD BF CE DE GF AG AC AL : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB) (hbac : ∠ b:a:c = ∟)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (hab : a ≠ b) (hfb : f ≠ b) (hce_len : |(c─e)| = |(b─c)|)
    (hcbd : ∠ c:b:d = ∟) (habf : ∠ a:b:f = ∟)
    (hgaBF : g.sameSide a BF) (hgcAB : ¬g.sameSide c AB) (hdaBC : ¬d.sameSide a BC)
    (hcag : between c a g) (hbah : between b a h)
    (haAL : a.onLine AL) (hlAL : l.onLine AL) (hlDE : l.onLine DE)
    (hALBD : ¬AL.intersectsLine BD)
    (hAGBF : ¬AG.intersectsLine BF) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hec : e ≠ c) (hdbCE : d.sameSide b CE)
    (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE)
    (hGFAB : ¬GF.intersectsLine AB)
    (hcoffAB : ¬c.onLine AB) (haoffBC : ¬a.onLine BC) (hdoffBC : ¬d.onLine BC)
    (hgoffAB : ¬g.onLine AB) (haoffBD : ¬a.onLine BD)
    (hABBC : AB ≠ BC)
    (hstep7 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) :
    ∠ d:b:a = ∠ f:b:c := by
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hABBF : AB ≠ BF := by euclid_finish
  have haoffBF : ¬a.onLine BF := by euclid_finish
  have hBDAB : BD ≠ AB := by euclid_finish
  -- seeds from betweenness (pasch_2)
  have step8_ahBF : a.sameSide h BF := by euclid_apply (helper_1_47_step8_ahBF a b h BF (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show ¬a.onLine BF; assumption)) (by euclid_assumption "" (show between b a h; assumption)))
  have step8_ahBD : a.sameSide h BD := by euclid_apply (helper_1_47_step8_ahBD a b h BD (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show between b a h; assumption)))
  have step8_ahBC : a.sameSide h BC := by euclid_apply (helper_1_47_step8_ahBC a b h BC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show between b a h; assumption)))
  have step8_agBC : a.sameSide g BC := by euclid_apply (helper_1_47_step8_agBC a c g BC (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show between c a g; assumption)))
  -- seeds from the squares
  have step8_gfAB : g.sameSide f AB := by euclid_apply (helper_1_47_step8_gfAB f g GF AB (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)))
  have step8_ecBD : e.sameSide c BD := by euclid_apply (helper_1_47_step8_ecBD b c d e DE BC BD CE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  have hfcAB : ¬f.sameSide c AB := by euclid_finish
  have step8_bcAL : ¬b.sameSide c AL := by euclid_apply (helper_1_47_step8_bcAL a b c d AL BD BC AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ∠ c:b:d = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)))
  have hde : d ≠ e := by euclid_finish
  have hdl : d ≠ l := by euclid_finish
  have hel : e ≠ l := by euclid_finish
  have hALDE : AL ≠ DE := by euclid_finish
  have step8_dle : between d l e := by euclid_apply (helper_1_47_step8_dle a b c d e l AL BD CE DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬b.sameSide c AL; assumption)) (by euclid_assumption "" (show d ≠ l; assumption)) (by euclid_assumption "" (show e ≠ l; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show AL ≠ DE; assumption)))
  have step8_B : a.sameSide c BD := by euclid_apply (helper_1_47_step8_B a b c d e l BD AL CE DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show e.sameSide c BD; assumption)) (by euclid_assumption "" (show between d l e; assumption)))
  have hdb : d ≠ b := Ne.symm hbd
  have step8_A : d.sameSide c AB := by euclid_apply (helper_1_47_step8_A a b c d BD BC AB (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)))
  have hBFAB : BF ≠ AB := Ne.symm hABBF
  have hACBF : AC ≠ BF := by euclid_finish
  have hcoffBF : ¬c.onLine BF := by euclid_finish
  have step8_D : c.sameSide a BF := by euclid_apply (helper_1_47_step8_D a b c f AB BC BF AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:f = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BF; assumption)) (by euclid_assumption "" (show ¬c.onLine BF; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show BF ≠ AB; assumption)) (by euclid_assumption "" (show AC ≠ BF; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)))
  have step8_C : f.sameSide a BC := by euclid_apply (helper_1_47_step8_C a b c f BF AB BC (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.sameSide a BF; assumption)) (by euclid_assumption "" (show ¬f.sameSide c AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)))
  euclid_apply (sum_angles_onlyif b d a c BD AB)
  euclid_apply (sum_angles_onlyif b f c a BF BC)
  euclid_apply (angle_symm c b a)
  linarith

end Elements.Book1
