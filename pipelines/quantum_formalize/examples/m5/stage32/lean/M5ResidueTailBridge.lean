import M5Checkpoint90
import Mathlib.Data.Fin.Tuple.Basic
open scoped BigOperators
namespace M5.ResidueTailBridge
def anchored {T k : ℕ} (hT : 0 < T) (r : Fin k → Fin T) : Fin (k + 1) → Fin T :=
  Fin.cons ⟨0, hT⟩ r
end M5.ResidueTailBridge
