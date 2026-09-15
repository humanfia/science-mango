# Stage 22: bounded connected supports

These four targets assemble the literal Section 5 construction. `anchoredTuple` means the designated first coordinate has residue zero; `tupleSupportGcd` is precisely the combined integer residue gcd with `T`. Both tuples may contain repeated residues, and either residue polynomial may vanish.

The first helper chooses a positive exponent from the packed first block and proves the remaining-exponent gcd hypotheses. The second obtains the bounded CRT parameter, freshness, and the original cutoff. The third establishes the repaired first support's cardinality, anchor, cutoff, and integer connectivity. The final target chooses that repaired support and combines these facts with the exact signature preservation identities.

The final second support is literally `packedSupport s`; it retains its bound `< w*T`, needed in the source's subsequent degree argument. The first support has the original bound `< packingCutoff w T`. The conclusion uses the combined support gcd without `T`, so it is the source's repaired integer connectivity condition. Equality with the tuple signature lets the caller substitute the prescribed `F`; no extra irreducibility, squarefreeness, distance, or ordering hypothesis is introduced.

The original proof requires `w >= 2` and `T > 0`; both are explicit. The theorem supplies bounded physical supports, not yet a bounded ambient order, effective recovery, or the full M5 birth theorem.

Stage19's six accepted proofs have been promoted only after receipt, exact source and target, draft, payload, and original compiled hash verification. Stage21 was subsequently accepted and its four proofs promoted after the same verification; both dependency gates are now resolved. No new proofs have been run in this preparation task.
