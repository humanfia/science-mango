import M6QueryResources
namespace M6.Transfer
/-- At most one frame per original coordinate: two bits per Option-bit pin,
plus three fixed-width continuation/index/counter words. This is an abstract
indexed-array allocation, not a claim about a Lean compiler call stack. -/
noncomputable def recoveryStackBits (R N : ℕ) : ℕ :=
  (List.finRange (2*N)).length * (4*N + 3*actualAddressBits R N)
end M6.Transfer
