import M5FeasibleSource
import Mathlib.Data.Finset.Sort

namespace M5.ResidueNecessity

def reduceTuple {w : ℕ} (T : ℕ) (hT : 0 < T) (u : Fin w → ℕ) : Fin w → Fin T :=
  fun i => ⟨u i % T, Nat.mod_lt (u i) hT⟩

end M5.ResidueNecessity
