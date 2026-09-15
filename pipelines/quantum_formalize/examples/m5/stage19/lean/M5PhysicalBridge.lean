import M5Accepted

namespace M5.PhysicalBridge

def remainingGcd (A B : Finset ℕ) (e : ℕ) : ℕ :=
  Nat.gcd ((A.erase e).gcd id) (B.gcd id)

end M5.PhysicalBridge
