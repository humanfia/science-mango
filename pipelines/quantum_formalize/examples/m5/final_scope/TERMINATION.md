# Original finite arithmetic termination and correctness

The source promises a terminating arithmetic workflow, not polynomial time, practical speed, generated machine code, a Lean executable, or a particular extraction backend. Assess the actual finite definitions and correctness links. The presence of `noncomputable` in Lean is neither a proof of termination nor a reason to reject an otherwise fully specified finite procedure.

## Finite evaluation

The n/R formulas range over a finite binary quotient and its finite character family. Their inputs use finite available-position sets, finite binomial sums or finite character-power sums. Integer divisor lists and finite polynomial residual-factor lists bound the Möbius/inclusion-exclusion sums. The dimension-zero quotient, empty products/tuples and repeated factors are covered by the existing identities.

It is legitimate for a semantic correctness proof to rewrite the arithmetic formula as a finite cardinality. It is not legitimate to redefine the evaluator to scan raw support pairs or to evaluate an unexplained sparse-realizability predicate. Preserve the arithmetic definitions in the final closure and inspect the call path used for recovery.

For period computation45, all candidate N lie in `1..2^natDegree F`; every check is polynomial divisibility. The accepted theorem proves nonemptiness and equality of the finite minimum to signaturePeriod. The procedure does not need a supplied realizing support. A fallback branch on inadmissible F is irrelevant under the stated monic/constant-one hypotheses, and must not be confused with failure on admissible F.

For birth43, the search domain is bounded by B and tested by the actual C. The existing construction proves some candidate succeeds when A>0. Thus there is no unbounded “search until success” and no existential count oracle. The minimum certificate proves both termination of the bounded search and minimality among all realizations, including those outside the scanned interval.

## Actual recovery links required

Generic binary recovery36 recurses on a natural fuel n. Generic residue recovery37 recurses on coordinate fuel and scans a finite list of at most T residues at each step. Their recursion/length/test-count proofs already express termination. The concrete46/47 integrations must identify the arithmetic branch function used by these recursions:

| Required link | Physical recovery46 | Residue recovery47 |
|---|---|---|
| State/decoder | Bool prefix over first-block then second-block positive positions | Prefix of first-block then second-block tail coordinates |
| Concrete count | Original selected/available conditional C formula | Original selected-prefix conditional R/Möbius formula |
| Initial state | Empty prefix count equals C(N,w,F) | Empty prefix count equals A(w,F) |
| Step partition | Parent equals exclude count plus include count | Parent equals sum over the T next residues |
| Terminal soundness | Positive full prefix decodes to anchored weight-w connected exact-F supports | Positive full prefix decodes to feasible anchored full/tail tuples |
| Finite bound | `m=2*(N−1)` binary decisions | `m=2*(w−1)` coordinates; at most `m*T` candidate tests |

The arithmetic count may be shown equal to a semantic prefix count via a bijection. That bijection is proof evidence; the recovery function should still call the arithmetic count. Impossible/overfull physical prefixes must have the intended zero count rather than relying on truncated natural subtraction to create false completions.

Once these links are proved and the generic recover theorems are instantiated with the actual functions, the original termination/correctness statement is present. Demanding runtime execution, code generation, a new decidability package, optimized factorization, or removal of every `noncomputable` annotation would add a new requirement.

Conversely, accepted generic recovery with a free `c` and assumed split/terminal axioms is not yet the original recovery theorem. An existential physical source, or exact arithmetic count alone, also does not identify the requested deterministic recipe recovery. This is a concrete original interface still to be connected, not a concern about Lean syntax.

## Source construction and composition

Recovered residue tuples feed the accepted occurrence packing and repair construction. Its remaining choices have explicit finite domains: select one of finitely many positive first-block exponents, and a CRT shift in the established bounded interval. The polynomial period is a finite search by45. Taking the first successful finite choice gives the deterministic arithmetic interpretation; no raw support-pair scan is introduced. Retain those bounded witnesses/correctness lemmas when assembling the constructor interface.

Independently, the bounded birth search followed by actual physical recovery yields a deterministic source and a birth recipe without scanning raw pairs. Thus a missing generated implementation of the particular packing constructor is not by itself an original-M5 gap. The explicit progression theorem must still supply its same-support/positive-step correctness; a mere existence theorem must not be described as executed code.

A final workflow correctness record can compose these finite stages: period → A → zero certificate or residue/source construction → bounded C minimum → birth recovery → arbitrary-order C decision and recovery. The later-order interface is a terminating query for each proposed N, not an algorithm required to enumerate all natural orders and halt.

## Current concrete integration plans (not acceptance claims)

The stage46 owner reports a Bool-prefix decoder in blockA-positive-position order followed by blockB-positive-position order, with the oracle equal to stage34 `completionC` on those decoded selected/available sets. The required equality to the stage44 valid-word prefix count includes impossible/overfull states. The final call is the existing binary recovery at `m=2*(N−1)`.

The stage47 owner reports `T=signaturePeriod F`, `m=2*(w−1)`, and the concrete oracle `c p = conditionalA w F (p.take (w−1)) (p.drop (w−1))`. A completion-pair/word-extension bijection connects it to the semantic prefix count; initial equality, branch sum and terminal validity then instantiate accepted37. The positive-count prefix invariant and decreasing coordinate fuel establish success within `m*T` candidate tests.

At this assessment these integrations are pending actual evidence. Their plans are mathematically the required original links, and should not be reported as already proved. Once their actual definitions and receipts discharge them, the pending labels should be removed without inventing another executable-runtime gate.
