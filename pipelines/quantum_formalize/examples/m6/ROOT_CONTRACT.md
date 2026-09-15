# Original M6 formalization contract

Source: `research/quantum_m6/research_checkpoints/m6_original_gate_closed_20260915/PROOF.md`, identified by SOURCE.json. This document maps that claim; it does not strengthen its gate. Exact Lean root definitions will be published with their hashes as their concrete modules are established.

## Domain and result

Anchored binary polynomial a,b have equal positive support weight; R=max(deg a,deg b)<N and gcd(N,supp(a),supp(b))=1. Preserve full F=gcd(a,b,X^N+1), including repeated factors and even N. At every allowed N, deg F>0 yields exact quantum distance and an actual minimum logical witness; F=1 yields no logical distance. The calculation uses finite indexed transfer, not physical-vector enumeration as its evaluator.

## Proof obligations

1. Connect polynomial quotient coefficients to the physical two-block spaces B=im L and C=ker syndrome. Prove B⊆C, boundary fibers of size2^deg F, and J's weight-preserving cycle/boundary correspondence; k=2deg F and X/Z distances agree.
2. Prove labeled closed length-N transfer walks correspond bijectively to indexed inputs, with convolution outputs. Keep two distinct labels at R=0 and do not divide by rotations. Matrix trace/array recurrence must compute this sum.
3. Prove binary character orthogonality and its coordinate factorization. Obtain the actual normalized trace formulas and Q enumerating C\B, with exact coefficient divisions, nonnegative coefficients, zero constant, total counts, and the no-logical case.
4. Prove swapped/inverted character pin positions. Actual pinned trace coefficients count pinned logical completions. Concrete zero-first recovery preserves a positive minimum-weight completion and returns a nonboundary zero-syndrome minimum vector in ≤2N extra paired queries. J yields the other type witness; the result equals CSS Pauli distance.
5. Prove termination and resources of the explicit indexed-array recurrence: O(N³4^R) bit work for distance, O(N⁴4^R) for witness and O(N²2^R) storage. Bounds must be linked to recurrence loop counts and coefficient/address widths, not assigned as arbitrary cost functions. At fixed R establish asymptotic improvement over4^N scanning and the declared nontrivial fixed-span family.
6. Preserve the documented recipe isometries and R=0 edge case. Record correspondence between mathematical recurrence and supplied Python default pin orientation; exclude deliberate wrong_orientation controls. Frozen finite reproductions remain evidence, never uniform proof premises.

## Evidence boundary

The complexity claim is for the indexed-array bit model. No unconditional Python interpreter timing guarantee, practical solver superiority, efficient arbitrary-span computation, M7/M8 result, invariant predictor or code-inequivalence classification is required. No new distance or resource requirement is being introduced: both are explicitly in original M6, unlike M5.

Auxiliary generic lemmas may use abstract spaces or oracle identities. The final root must instantiate them with the actual cyclic code and actual transfer evaluator; their correctness cannot remain free root assumptions. Source/definition hashes, actual proof imports, exact root type, combined compilation and independent standard-axiom audit establish final acceptance. Historical scheduler `m5_formalized=false` is an unrelated constant and remains unchanged; a dedicated M6 root record will express completion only after the actual checks succeed.
