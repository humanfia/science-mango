# Actual sequential objective comparator

The Pareto scan records all-le by early rejection and any-strict by a Boolean accumulator. The lex scan stops at its first unequal integer coordinate. Both traverse actual Fin-indexed objectives in order with finite fuel, retaining all ties and the empty-objective behavior. Each executed integer comparison is counted explicitly, with at most two per visited coordinate.

Six exact targets establish interval semantics, count bounds, equivalence to the original Selection.better and at most 2*m <= 2*(m+1) integer comparisons. This supplies the original objective-count factor. It does not charge external label evaluation for free or claim Lean runtime complexity; the original signed-integer bit-operation model must separately charge those comparisons before the full B-bit resource claim.
