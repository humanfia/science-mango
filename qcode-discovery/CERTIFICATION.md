# Universal qLDPC certification

The fail-closed certificate pipeline accepts three claim forms:

- BB parameters: `ell`, `m`, `A_terms`, `B_terms`
- arbitrary CSS matrices: `H_X`, `H_Z`
- PBB parameters or an arbitrary `symplectic_stabilizer`

Matrices may be JSON arrays of binary rows, arrays of bit strings, or the
packed row format emitted in a certificate.  PBB certificates bind both the
polynomial construction and the complete symplectic stabilizer matrix.

```bash
python scripts/build_certificate.py claim.json \
  --output certificate.json \
  --timeout-per-logical 300 \
  --total-timeout 7200

python verify.py certificate.json
python scripts/finalize_challenge.py certificate.json
```

`verify.py` reconstructs matrices and logical bases, checks the concrete
minimum-weight witness in every direction, and reruns every MILP.  A release
is accepted only if the known-answer artifact is valid, all `2k` directions
are zero-gap optima, the code is connected with check weight and qubit degree
at most six, the pinned known-code registry reports it novel, and the exact
parameters satisfy a challenge win condition.

The registry is rebuilt and integrity checked with:

```bash
python scripts/build_known_registry.py
pytest -q tests/test_registry.py
```

It pins source hashes and canonical representatives for CSS and non-CSS
codes.  The checked-in version contains the literature/ECZoo QCGA reference
set plus the local qcode-discovery CSS and PBB publication catalogs.

Targeted PBB search uses static fail-fast checks before any MILP:

```bash
python scripts/search_real_win.py \
  --ell 6 --m 6 --trials 50000 --seed 20260724
```

The search output records every candidate that reaches MILP, including
feasible low-weight counter-witnesses that rigorously exclude a win.
