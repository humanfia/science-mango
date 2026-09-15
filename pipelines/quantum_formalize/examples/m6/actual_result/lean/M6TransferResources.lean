import M6Transfer
namespace M6.Transfer

-- A scatter loop visits each source state, both bit-labelled edges, every
-- coefficient slot and each of the at-most-three edge coefficients.
abbrev ScatterEvent (R N : ℕ) := Memory R × Bit × Fin (2*N+1) × Fin 3

def coefficientBits (R N : ℕ) : ℕ := R + 3*N + 2
def addressBits (R N : ℕ) : ℕ := R + 2*N + 4

def eventBitCharge (R N : ℕ) : ℕ :=
  4 * coefficientBits R N + 4 * addressBits R N + 8

noncomputable def traceCoefficientOps (R N : ℕ) : ℕ :=
  Fintype.card (Memory R) * N * Fintype.card (ScatterEvent R N)

-- Include clearing each destination layer for every start/layer in the model.
noncomputable def traceWorkModel (R N : ℕ) : ℕ :=
  (traceCoefficientOps R N + (2^R)^2 * N * (2*N+1)) * eventBitCharge R N

def traceStorageModel (R N : ℕ) : ℕ :=
  2 * 2^R * (2*N+1) * coefficientBits R N +
  (2*N+1) * coefficientBits R N + 2 * 2^R * (R+2) + 2*N + 16

def addressLocations (R N : ℕ) : ℕ := 16 * 2^R * (N+1)^2

end M6.Transfer
