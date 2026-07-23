# Qcode structural novelty gate

The qcode challenge flow rejects CSS candidates that are merely different
representations of known or already-selected codes.

The gate runs after candidate scoring/MILP and before result persistence:

1. build the colored CSS Tanner graph (qubits, X checks, Z checks);
2. compute its BLISS canonical form and SHA-256 digest;
3. compare against the literature registry;
4. for every match, extract the full qubit/X-row/Z-row isomorphism;
5. replay that mapping directly against both `H_X` and `H_Z`;
6. reject the candidate unless it is a new structural class.

Candidates that survive carry a `structural_novelty` audit object in the run
evaluation log. The Archon-to-Lean selector requires `novel: true` when these
audits are present and keeps only the highest-scoring representative for each
canonical digest.

The check is enabled by default:

```bash
cd qcode-discovery
uv run python main.py --quick --lattices 12,6
```

It can be disabled for diagnostic experiments only:

```bash
uv run python main.py --quick --lattices 12,6 --no-structural-dedup
```

BLISS performs the graph-isomorphism search. Lean remains the trusted checker
for generated code-property theorems; it does not search for graph
isomorphisms. The explicit matrix replay prevents a canonical-hash match alone
from being treated as an equivalence certificate at the final persistence
gate.
