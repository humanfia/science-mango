# Source-pinned finite Lean certificates

`certificate.py` turns a human-reviewed finite model of a pinned paper excerpt
into a certificate that Lean checks. It is deliberately not an automatic
natural-language theorem extractor: the excerpt-to-JSON modeling step remains
explicit and reviewable.

From the `wang_zahl_kakeya_dimH` Lake project, run:

```bash
python3 tools/paper_to_lean/certificate.py \
  tools/paper_to_lean/examples/interval_classification_certify.json \
  --output /tmp/paper-to-lean-certificate \
  --project .
```

The output path must be fresh. A zero exit status means all of the following
held:

- the selected UTF-8 source excerpt matched its explicit SHA-256 and remained
  inside the trusted source root;
- the strict JSON schema, unique object keys, identifiers, types, AST limits,
  and rendering budget passed;
- bounded Z3 classified `constraints ∧ ¬claim` as unsatisfiable or produced a
  concrete counterexample;
- warning-as-error Lean checking succeeded before its deadline and the
  certificate did not change while being checked;
- exactly one axiom report was bound to the generated target, with no axioms
  beyond `propext`, `Classical.choice`, and `Quot.sound`.

The artifact directory contains the pinned excerpt, SMT-LIB model,
`Certificate.lean`, and a hash-rich `report.json`. An unsatisfiable result
generates the modeled theorem; a satisfiable result generates and kernel-checks
the concrete counterexample instead of claiming the theorem.

Run the adversarial regression suite with:

```bash
python3 -m unittest -v tools/paper_to_lean/tests/test_certificate.py
```

Only `certificate.py` is the production certificate authority. Other
paper-to-Lean scripts in local scratch state are research prototypes.
