import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_13_s10
    (s7 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c)
    (s8 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c)
    (s9 : (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
             (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
             (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c)) :
    ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c := by
  exact s9 s8 s7

end Elements.Book1
