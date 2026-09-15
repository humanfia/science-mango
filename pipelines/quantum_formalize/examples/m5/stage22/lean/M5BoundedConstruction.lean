import M5Checkpoint72
import M5PhysicalBridgeAccepted
import M5SignatureCongruenceAccepted

namespace M5.BoundedConstruction

def anchoredTuple {w T : ℕ} (r : Fin w → Fin T) : Prop :=
  ∀ i : Fin w, i.val = 0 → (r i).val = 0

def tupleSupportGcd {w T : ℕ} (r s : Fin w → Fin T) : ℕ :=
  Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val))
    (Finset.univ.gcd (fun i : Fin w => (s i).val)))

end M5.BoundedConstruction
