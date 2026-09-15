# Actual residue recovery from conditional arithmetic A

Concrete linkage is accepted in the full eight-node experiment, not an additional M5 assumption. Complete accepted stage42, stage37 and stage44 closures have been verified; the full target/import preflight passed.

Set T = signaturePeriod F, k = w-1 and m = 2*k. The concrete recovery oracle on a list u of residues is conditionalA w F (u.take k) (u.drop k). Its definition contains only the accepted finite divisor/factor/character arithmetic. A semantic finite set of full words is introduced exclusively for correctness proofs.

Encode a completion pair (a,b) as (u.take k ++ List.ofFn a) ++ (u.drop k ++ List.ofFn b). For u.length <= m this gives a bijection between feasible completion pairs and valid full words extending u. Polynomial sums and raw-coordinate gcds are preserved; repetitions, cancellations, empty prefixes and terminal empty completions remain allowed. Overfull prefixes retain stage42's zero guard.

Accepted proof dependencies: generic completion-word split and cardinality bijection; selected-polynomial and prefix-gcd append identities; feasibility correspondence; exact concrete-oracle prefix count; arithmetic initial value plus branch partition and terminal validity; stage37 recovery instantiated with this concrete oracle.

The final theorem has w>0, F monic and F(0)=1 and positive A as input, with no abstract oracle-correctness hypotheses. It returns a length 2*(w-1) residue word with raw gcd 1 and exact full polynomial signature F. The accepted stage37 algorithm preserves positive-prefix count, appends one residue per step, decreases remaining fuel and uses at most 2*(w-1)*T arithmetic candidate tests. This is a finite-decision correctness/test-count statement, not an extra executable-runtime refinement requirement.
