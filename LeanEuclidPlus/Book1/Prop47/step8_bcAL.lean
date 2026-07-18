import SystemE
import Book1.Prop32.Main
import Helpers.Pasch
import Book1.Prop47.step8_bcAL_cross
import Book1.Prop47.step8_bcAL_perp
import Book1.Prop47.step8_bcAL_bmc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The altitude foot m = AL ∩ BC lies strictly between b and c (right angle at a ⟹ acute base
-- angles ⟹ foot inside), hence b and c are on opposite sides of the perpendicular AL.
theorem helper_1_47_step8_bcAL
    (a b c d : Point) (AL BD BC AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbac : ∠ b:a:c = ∟)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hcbd : ∠ c:b:d = ∟)
    (hdaBC : ¬d.sameSide a BC) (hdoffBC : ¬d.onLine BC)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hbd : b ≠ d)
    (haoffBC : ¬a.onLine BC) (haoffBD : ¬a.onLine BD) :
    ¬b.sameSide c AL := by
  have hBDBC : BD ≠ BC := by euclid_finish
  have step8_bcAL_cross : AL.intersectsLine BC := by euclid_apply (helper_1_47_step8_bcAL_cross a b d AL BD BC (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show BD ≠ BC; assumption)))
  euclid_apply (intersection_lines AL BC) as m
  have hmAL : m.onLine AL := by euclid_finish
  have hmBC : m.onLine BC := by euclid_finish
  have ham : a ≠ m := by euclid_finish
  have hmb : m ≠ b := by euclid_finish
  have hcb : c ≠ b := Ne.symm hbc
  have hABAL : AB ≠ AL := by euclid_finish
  have hBCAL : BC ≠ AL := by euclid_finish
  have step8_bcAL_perp : ∠ a:m:b = ∟ := by euclid_apply (helper_1_47_step8_bcAL_perp a b c d m AL BD BC (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ∠ c:b:d = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show a ≠ m; assumption)) (by euclid_assumption "" (show m ≠ b; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)))
  euclid_apply (extend_point BC b c) as d'
  euclid_apply (proposition_32 a b c d' AB BC AC)
  have hmc : m ≠ c := by euclid_finish
  have hACAL : AC ≠ AL := by euclid_finish
  have step8_bcAL_bmc : between b m c := by euclid_apply (helper_1_47_step8_bcAL_bmc a b c m AB BC AC AL (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AL; assumption)) (by euclid_assumption "" (show AC ≠ AL; assumption)) (by euclid_assumption "" (show BC ≠ AL; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show m ≠ b; assumption)) (by euclid_assumption "" (show m ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ m; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:m:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟; assumption)))
  euclid_apply (Elements.not_sameSide_of_between b m c AL)
  euclid_finish

end Elements.Book1
