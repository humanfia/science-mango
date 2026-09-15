import M6TransferActualResources
import M6TransferPartialResources

namespace M6.Transfer

def FitsSigned (R N : ℕ) (z : ℤ) : Prop :=
  z.natAbs < 2^(coefficientBits R N - 1)

structure IndexedArrayGuarantee (R N : ℕ) [NeZero N]
    (W : ℕ → Memory R → Bit → Polynomial ℤ) : Prop where
  trace_exact : scalarTracePolynomial W N =
    ∑ h : Input N, ∏ i : ZMod N, W i.val (memoryAt h i) (h i)
  work_bound : actualTraceWork R N ≤ 16384 * N^3 * 4^R
  storage_bound : actualTraceStorage R N ≤ 4096 * N^2 * 2^R
  addresses_fit : actualTraceStorage R N < 2^(actualAddressBits R N)
  layer_prefix_fits : ∀ (start : Memory R) (i : ℕ), i < N →
    ∀ (k : ℕ) (addr : CoefficientAddress R N),
      FitsSigned R N (((scatterEventList R N).take k).foldl
        (scatterUpdate (W i) (scalarLayers (N:=N) W start i)) (fun _ => 0) addr)
  event_term_fits : ∀ (start : Memory R) (i : ℕ), i < N →
    ∀ e : ScatterEvent R N,
      FitsSigned R N (eventTerm (W i) (scalarLayers (N:=N) W start i) e)
  trace_prefix_fits : ∀ (k : ℕ) (d : Fin (2*N+1)),
    FitsSigned R N ((((Finset.univ : Finset (Memory R)).toList.take k).map
      (fun start => scalarLayers (N:=N) W start N (start,d))).sum)

end M6.Transfer
