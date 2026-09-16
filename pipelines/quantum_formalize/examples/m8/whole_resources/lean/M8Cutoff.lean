import Mathlib
namespace M8.Cutoff
/-- Fixed revised-M8 logarithmic orbit-span threshold. -/
def limit (N : ℕ) : ℕ := min (N-1) (Nat.log 2 (N+1))
end M8.Cutoff
