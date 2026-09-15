import M6TransferScatter
import M6TransferResourcesAccepted
namespace M6.Transfer
-- Wide enough for all bit-addressed allocations including the actual event list.
def actualAddressBits (R N : ℕ) : ℕ := R + 4*N + 16
-- Per event: coefficient arithmetic, record construction/addressing, and the
-- explicit allowance for two packed length-(R+1) parity computations and pins.
def actualEventBitCharge (R N : ℕ) : ℕ :=
  4 * coefficientBits R N + 16 * actualAddressBits R N + 128 * (R+1) + 128

noncomputable def actualTraceWork (R N : ℕ) : ℕ :=
  (Fintype.card (Memory R) * N * (scatterEventList R N).length +
    (2^R)^2 * N * (2*N+1)) * actualEventBitCharge R N

noncomputable def actualTraceStorage (R N : ℕ) : ℕ :=
  traceStorageModel R N +
  (scatterEventList R N).length * (4 * actualAddressBits R N + 8) +
  64 * (coefficientBits R N + actualAddressBits R N) + 4*N

end M6.Transfer
