# M7 compact arithmetic selector

**Status: original M7 is complete at symbolic constructive-selector strength.**

[Acceptance decision](integration-decision.json) · [Independent review A](reviewer_a.json) · [Independent review B](reviewer_b.json)

[Full symbolic candidate](PROOF.md) · [Exact candidate JSON](candidate.json) · [Frozen dependencies](dependency-manifest.json) · [Finite replay](verification-replay.json)

Candidate SHA-256: `44e9358d34dd671ce76b39cd5c1f64b6a16b5229b9d98ce0e21d813b557c7a99`.

## Mathematical result

For every finite order N and positive equal support weight w in the declared connected cyclic two-block binary CSS recipe family, the proposed algorithm constructs every requested recipe class and selects every optimum, including all tied actions or distinct ordered physical presentations.

The exact equivalence group consists of independent translations, one common unit multiplier, and block exchange. Recipe classes do not assert quantum-code inequivalence.

| Component | Construction |
|---|---|
| Complete generation | M5 conditional arithmetic minus compact counts of already emitted orbits; one recovered leaf per new class |
| Compact orbit count | Product of independent single-block shift counts, divided by the full stabilizer |
| Labels and witnesses | Exact M6 transfer enumerators and coordinate pinning; NoLogical when k=0 |
| Constraints and optima | Exact dimension, literal-signature modes, distance, joint realizable locality, Pareto or lexicographic comparison |
| All placement ties | Finite winning-action predicate and factorized least-preimage decoder |
| Completeness certificate | Recompute arithmetic, final zero residual, exact labels, winners, rejection reasons and empty answers |

Generation does not scan Cartesian support pairs or expand full pair orbits. The algorithm can still require exponential arithmetic, many quotient classes and many action comparisons; requested output can itself be large. Arbitrary-span efficiency is M8 and remains open.

## Evidence boundaries

The full artifact is a natural-language symbolic proof with a constructive finite algorithm and verifier. It is not Lean certification or a complete software implementation of every proved query/replay feature. The prototype implements the documented subset. Finite tests and review verdicts are separate evidence, never mathematical premises.

The final candidate revises obsolete milestone-status prose from the first compact integration. Its mathematical sections 2–11 are unchanged. [Amendment provenance](provenance/amendment-provenance.json), [exact diff](provenance/scope-amendment.diff), and [harness scope patch](provenance/harness-scope.patch) are retained. The corrected harness changes scope prompts and required proof inputs; its mathematical review and acceptance machinery is unchanged. Historical review votes were not imported into this final audit.

## Reproduce the finite checks

The verification scripts use only the Python standard library. From this directory:

```bash
cd verification
python3 verify_selector_compact.py
python3 verify_placements.py
python3 verify_coverage_controls.py
```

Archived-source replay passed:

- 29 generation cases: every positive weight at N=1,…,6, plus full-signature sectors at N=7,w=3.
- 75 optimization queries: five settings for every positive weight at N=1,…,5.
- 12 complete-placement queries, including duplicate-action ties and duplicate-free physical reconstruction.
- Missing-class, duplicate-class and wrong-root-count corruption controls; generation also passed with raw reference functions disabled.

`verify_selector_compact.py` uses raw enumeration only in independent finite reference routines. `selector_complete.py` adds complete action/presentation decoding for the prototype query subset. The scripts do not implement the full cap/lexicographic/placement-sector/extension and certificate-output contract. The proof specifies those interfaces explicitly.

## Original milestone boundary

M7's original gate is "All certified optima for requested parameters without raw scan". The candidate derives the invoked M5 finite-order counts and M6 exact-distance identities directly. It does not rely on an assumed complete transversal, an unresolved distance oracle, historical catalogue labels or a SELF premise. The two final independent reviews checked this entire mathematical construction and its fidelity to that gate; the controller acceptance decision records the clause-by-clause assessment.
