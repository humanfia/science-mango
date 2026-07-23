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

All three commands, `certify_run.py`, `verify_release.py`, formalization, and
CI use `evaluation/certificate_dispatch.py` as the single fail-closed routing
table.  Releases are replayed with `verify_release.py` before any Lean module
is generated; generic CSS, PBB, and generic symplectic certificates are routed
to `bridge_universal.py`.

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

python scripts/search_expanded_ansatz.py \
  --shapes 6x6,9x6,12x6 \
  --term-splits 2+2,2+3,3+2,2+4,4+2,3+3 \
  --trials 50000 --seed 20260728
```

The expanded search covers sparse CSS/BB checks of total weight four through
six instead of only the original fixed 3+3 PBB subset family.  Search output
records every candidate that reaches MILP, including concrete low-weight
counter-witnesses that rigorously exclude a win.  Existing PBB search artifacts
can be upgraded to the same self-contained format with:

```bash
python scripts/backfill_search_witnesses.py results/real_win_search*.jsonl \
  --summary results/real_win_search_summary.json
```

For a verified release, Archon invokes `bridge_universal.py`; Lean reconstructs
the full symplectic stabilizer and complete `2k` logical quotient basis, checks
their ranks and symplectic pairing, and proves the exact-distance lower bound
with `bv_decide`.
