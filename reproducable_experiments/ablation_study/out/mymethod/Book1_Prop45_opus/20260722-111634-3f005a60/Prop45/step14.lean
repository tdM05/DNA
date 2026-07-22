import SystemE
import Book1Variants.Prop29
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step14 (g h l m : Point) (HM GL GH LM : Line)
    (hhHM : h.onLine HM) (hmHM : m.onLine HM)
    (hgGL : g.onLine GL) (hlGL : l.onLine GL)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
    (hssHLM : h.sameSide g LM)
    (hpar1 : ¬HM.intersectsLine GL) (hpar2 : ¬GH.intersectsLine LM) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  have hhoffLM : ¬ h.onLine LM := same_side_not_on_line h g LM hssHLM
  have hne : LM ≠ GH := fun heq => hhoffLM (heq ▸ hhGH)
  have hpar2' : ¬(LM.intersectsLine GH) := by euclid_finish
  have hmssl : m.sameSide l GH := Elements.sameSide_of_parallel_both m l LM GH hmLM hlLM hne hpar2'
  euclid_apply (proposition_29''''' m l h g HM GL GH)
  euclid_finish

end Elements.Book1
