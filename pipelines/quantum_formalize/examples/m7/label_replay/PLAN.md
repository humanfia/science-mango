# Actual label certificate replay — preparation only

No new model workers are started while CompactStorage is running. These interfaces are proposed, not frozen or accepted.

The existing M6.ActualTransfer.Q computes normalized boundary/character **scalarTracePolynomial** recurrences; M6.ActualTransfer.solve calls M6.Pinned.solve on that exact Q. Pinned.solve scans coefficients 0..2N, then calls Pinned.recover on List.finRange (2N); recover calls the existing Pinned.choose, whose decision is the actual tentative zero-pin coefficient. Thus replay can recompute the original arithmetic rather than consult a semantic distance oracle or an assumed PointwiseCorrect property.

Proposed certificate fields are: the actual full signature polynomial; a fixed Fin(2N+1)-indexed integer coefficient vector for Q at free pins; actual solve answer Option(distance,vector,callCount); and the complete finite pin-step data for the selected distance (empty when the actual scan returns none). Each pin step stores the index, pre-state pins, the queried zero-pin coefficient when unassigned, and the post-state produced by the existing choose. The trace constructor recurses over the existing finRange and invokes the existing choose with P ↦ (Q P).coeff d. It is an audit trace of that function, not a replacement choice oracle.

The Boolean checker compares the certificate's signature, coefficient vector, answer and full pin-step list with these actual computations. All comparisons are finite data comparisons. It does not call Classical.decide on logical-witness correctness or Irreducible, and does not merely compare hashes. The self-produced certificate passes by equality. A separate small trace lemma identifies the final pins/call accumulator with the existing recover, so the logged branch data is tied to the actual solve.

Bounded target plan (about four targets):

1. **trace_recover**: exact trace endpoint and summed query counts equal the existing Pinned.recover at the actual Q coefficient function and fixed finRange.
2. **check_sound**: checker=true implies exact full signature, every coefficient 0..2N, actual solve result, and exact complete pin-step data agree with the recorded fields.
3. **self_check**: constructing the certificate from the actual recurrence and solve passes the same checker; no outside correctness assertion is consumed.
4. **checked_physical_answer**: for original equal-card anchored connected supports, checker success implies the recorded none iff actual signature degree zero, and every recorded some(d,v,k) is the actual query distance with v in physical LX, Jv in LZ, both weight d, and k≤2N. Use accepted ClosedSolve.closed_pointwise and existing Transport definitions. No PointwiseCorrect, AnswerCorrect, or supplied-distance premise is public. Root's generated_labels specialization is a separate explicit dependency gate.

Full polynomial equality need not be separately asserted: the required coefficient record is exactly the finite 0..2N range. If a polynomial reconstruction field is used, its degree bound and reconstruction equality must be explicit rather than inferred from a truncated list. No new runtime extraction, host timing, parser or compiler correctness target is introduced.

Local interface evidence: m6/final/seal/lean/M6ActualTransfer.lean definitions boundaryTrace/characterTrace/Q/solve; M6Pinned.lean definitions firstPositive/choose/recover/solve. ClosedSolve and QualityTable canonical receipts already discharge actual physical correctness and actual cached distance. Factor certificates are handled in sibling factor_replay/PLAN.md with a real bounded-divisor test, not an abstract irreducibility oracle.
