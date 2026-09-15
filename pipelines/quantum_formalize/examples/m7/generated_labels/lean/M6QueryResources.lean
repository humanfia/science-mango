import M6TransferActualResources
namespace M6.Transfer
/-- Two normalization shifts, subtraction, and positive-coefficient scan per output slot. -/
abbrev PostEvent (N : ℕ) := Fin (2*N+1) × Fin 4
/-- Two extra bits cover signed subtraction and transient carry. -/
noncomputable def queryCoefficientBits (R N : ℕ) := coefficientBits R N + 2
/-- Fixed-width shift/subtract/test allowance, plus constructing shift amounts. -/
noncomputable def postWork (R N : ℕ) := Fintype.card (PostEvent N) * (8 * queryCoefficientBits R N + 16) + 8*(N+1)
noncomputable def pairedQueryWork (R N : ℕ) := 2 * actualTraceWork R N + postWork R N
/-- Reuse the trace workspace; retain both traces and the result, plus registers and pins. -/
noncomputable def pairedQueryStorage (R N : ℕ) := actualTraceStorage R N + 8*(2*N+1)*queryCoefficientBits R N + 16*(N+1)
/-- A full pin-array copy/update/test allowance, charged even when updates can be reused. -/
noncomputable def pinMaintenanceWork (R N : ℕ) := 16*(2*N+1) + 16*queryCoefficientBits R N
/-- Work after one real preprocessing call of measured charge e. -/
noncomputable def distanceWork (R N e : ℕ) := e + pairedQueryWork R N
/-- Initial query, k actual recovery queries, their pin updates, and final vector decode. -/
noncomputable def witnessWork (R N e k : ℕ) := e + (k+1)*pairedQueryWork R N + k*pinMaintenanceWork R N + 8*(N+1)
/-- Allow preprocessing storage to coexist, a conservative bound for sequential reuse. -/
noncomputable def solveStorage (R N slots : ℕ) := slots + pairedQueryStorage R N
end M6.Transfer
