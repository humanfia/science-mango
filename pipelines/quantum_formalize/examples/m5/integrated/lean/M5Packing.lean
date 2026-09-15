import M5Foundation
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

namespace M5.Packing

def priorOccurrences {w T : ℕ} (r : Fin w → Fin T) (i : Fin w) : Finset (Fin w) :=
  Finset.univ.filter (fun h => h < i ∧ r h = r i)

def occurrenceTag {w T : ℕ} (r : Fin w → Fin T) (i : Fin w) : ℕ :=
  (priorOccurrences r i).card

def packedValue {w T : ℕ} (r : Fin w → Fin T) (i : Fin w) : ℕ :=
  (r i).val + occurrenceTag r i * T

def packedSupport {w T : ℕ} (r : Fin w → Fin T) : Finset ℕ :=
  Finset.univ.image (packedValue r)

end M5.Packing
