# Original Python and formal indexed-array correspondence

The frozen original implementation is `research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/dependencies/scripts/m6_transfer_validation_20260915.py`. Its hash and a fresh finite reproduction are in REPRODUCTION.json. This mapping is a static review, not a formal verification of the Python interpreter or its runtime performance. Complete M6 acceptance also requires the Lean root.

| Original operation | Lean representation / obligation |
|---|---|
| Integer polynomial bits; XOR high-term cancellation in remainder and gcd | M6.Euclid dense binary coefficients, cancellation, explicit degree scanning and Euclid recursion |
| `(1 << N) | 1`, full gcd without square-free reduction | M6.Cyclic.modulus N and signature; repeated factors retained |
| `window=(memory<<1)|bit`, successor mask | M6.Transfer.output / shift; memoryAt stores the immediately preceding input first |
| Two loop entries for bit 0 and bit 1 | Bit-indexed edge sum and scatter event list; no merging of labels at R=0 |
| Boundary pin positions i,N+i | ActualTransfer.boundaryWeight with leftIndex/rightIndex |
| Character pin positions N+(-i)%N,(-i)%N | ActualTransfer.characterWeight with rightIndex(-i),leftIndex(-i) |
| Degree-two product of coordinate factors | Character.boundaryFactor / pinnedCharacterFactor and accepted factor bounds |
| Add `c*weight` into destination degree j+k | Transfer.scatterUpdate and scatterLayer; scalarLayers repeats the actual sparse event recurrence |
| Sum closed entries for every indexed starting state | Transfer.scalarTracePolynomial; no quotient by cyclic rotation |
| Divide coefficients by 2^f and 2^N, subtract | Normalize.divide and ActualTransfer.Q; exact division follows from actual fiber and character identities |
| First nonzero Q coefficient; zero-first pin query | Pinned.firstPositive / choose / recover and ActualTransfer.solve; coefficient nonnegativity makes positive and nonzero agree |

Python caches edge/weight tables and skips zero entries; the formal indexed-array implementation uses a bounded event list and can compute parities at each event. The declared bit-model resource proof counts its own event storage, coefficient arrays, indices and parity operations. It does not assign that bound to Python dictionary or interpreter overhead. Dense matrix recurrences serve as algebraic semantics; the formal evaluator is the sparse scatter recurrence.

The independent `matrix_sets` enumeration is used only for finite reproduction and orientation controls. Neither it nor its successful test results may appear as a uniform theorem hypothesis. The deliberate `wrong_orientation=True` branch is a negative control, excluded from the intended algorithm.
