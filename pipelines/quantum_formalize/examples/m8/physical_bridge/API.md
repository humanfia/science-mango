# Actual physical bridge

The public namespace is `M8.PhysicalBridge`. `signature c` is the existing full polynomial gcd `M7.RecipeSignature.signature c`. `solve c` is `M6.ActualTransfer.solve N` on the literal support polynomials. `undo g` is the existing coordinate permutation `M7.Transport.Xmap (M7.Action.inverse g)`.

`Valid w c` records the two actual support cardinalities and the unique M7 within-block-difference connectedness predicate. `Anchored (act g c)` records both actual zero memberships; the parent anchor-discovery proof supplies this property for its retained tuple. No correctness, distance, or minimum-span premise is supplied.

The four frozen target types are in `graph.json`:

- `signature_transport_degree`: full gcd degree is invariant under the actual recipe action.
- `pointwise_optimizer`: a valid raw recipe and actual anchored presentation satisfy sealed `M6.Final.PointwiseCorrect`. Its projections expose the literal trace/pin enumerator identities, physical CSS answer correctness, indexed execution and storage contracts.
- `noLogical`: the actual optimizer returns `none` exactly when the original full gcd equals one.
- `minimum_original_witness`: if that gcd differs from one, the actual solve returns a minimum; undoing the recorded action gives a nonboundary original-coordinate LX vector of that weight, actual physical quantum distance equals that weight, and every original LX vector is at least as heavy. The actual pin count is at most `2*N`.

Accepted dependencies are promoted from the canonical `closed_solve` and `actual_signature` receipts with every canonical manifest and imported Lean source hash checked. `IMPORT_PROVENANCE.json` records those checks and any harmless declaration-order equivalence. In particular, the physical CSS quantum-distance definition is the independent Pauli union-support minimum, not a definition assigning a desired component minimum. M6 already proves its equality with the pure logical minimum and the exact finite trace/pinning recurrence, including both labelled loops at zero memory and all polynomial multiplicities.

These are general physical correctness interfaces used within the revised M8 fixed logarithmic-span recognizer. They do not assert an unrestricted-span polynomial runtime. The M8 cutoff, discovery/rejection, explicit covered families and sequential simulation costs are separate parent obligations. Nothing here enlarges M8 into M9.
