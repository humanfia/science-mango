# Selected/available single-block arithmetic count

Given disjoint selected A and available W, n(P,W,k,z_A) exactly counts extensions U⊆W of size k for which P divides the final support polynomial of A∪U. Here z_A is the selected polynomial's quotient residue; in characteristic2 it is the residue the extension must cancel.

This is the source conditional-recovery block formula. It uses the accepted n arithmetic definition, not a cardinality replacement. No anchor assumption is needed for this local identity; the global conditional pair theorem will provide anchors and total weight checks. Negative deficits/overfull selected sets must be handled by that global wrapper, not Nat subtraction silently underflowing here.
