# Stage 19 scope

These six frozen targets supply the arithmetic hypotheses used in Section 5 of the reviewed M5 proof. They use the literal per-residue occurrence packing from `M5.Packing`, with repetitions retained. The combined tuple gcd includes `T`, exactly as in residue feasibility. No nonempty tuple hypothesis is imposed on the two packing identities.

`remainingGcd A B e` takes the gcd of every member of `A.erase e` and `B`. This equals the source's gcd of the remaining positive exponents because zero entries do not change a natural gcd. Positivity and the upper bound follow from the second block alone: its cardinality is at least two, it contains zero, and all members are below `K`. The selected first-block exponent is only required to belong to `A` for the gcd identity; its positivity will be needed later to preserve the anchor during replacement.

The cutoff target is the original strict bound `e + k*T < w*T*(T+2)`, with the packing and CRT bounds as hypotheses. It does not assert a stronger repaired bound. There are no squarefreeness, distance, inherited, or anchored-ordering assumptions.

These are specification/type preflights, not accepted proofs. Remaining work includes actually replacing the chosen exponent, preserving the physical support properties and polynomial signature, and assembling the bounded-source theorem.
