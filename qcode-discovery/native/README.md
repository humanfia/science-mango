# CaDiCaL BCP-aware adaptive cuber (TEST_ONLY)

`cadical_bcp_aware_cuber_v1.cpp` builds a prefix-free, mutually exclusive,
exhaustive cube cover.  It is intentionally not wired into the production
paper400 runner.

The implementation differs from a fixed-depth cuber in two important ways:

- `simplify(0)` and `fixed()` exclude variables already assigned by root-level
  unit propagation.  `lookahead()` is followed by `inconsistent()` because
  CaDiCaL 1.9.5 does not expose lookahead-derived UNSAT through `status()`.
- The frontier is split best-first.  Propagation-terminal leaves stay in the
  cover but are never split again, so the split budget is spent on the largest
  remaining live leaf.  Candidate variables are ranked by two-sided BCP,
  preferring zero immediate-conflict sides and minimizing the worst child.

Build against an audited CaDiCaL 1.9.5 static library:

```bash
g++ -O2 -std=c++17 -Wall -Wextra -Werror \
  -I/PINNED/CADICAL/src \
  native/cadical_bcp_aware_cuber_v1.cpp \
  /PINNED/CADICAL/build/libcadical.a -lpthread \
  -o /ABS/TEST_ONLY/cadical_bcp_aware_cuber_v1
```

Run:

```bash
/ABS/TEST_ONLY/cadical_bcp_aware_cuber_v1 \
  INPUT.cnf TARGET_LEAVES OUTPUT_PREFIX [MAX_CANDIDATES]
```

The output includes `.cubes`, `.icnf`, individual leaf CNFs, a tree TSV, a
leaf TSV, and a TEST_ONLY coverage JSON.  Propagation terminal labels are
heuristics, not proof certificates.  Before scientific use, independently
prove the cover complement UNSAT and generate/verify a proof for every leaf.

The opt-in integration tests require an already-built binary:

```bash
CADICAL_BCP_CUBER_BIN=/ABS/TEST_ONLY/cadical_bcp_aware_cuber_v1 \
  python -m pytest tests/test_cadical_bcp_aware_cuber_v1.py -q
```
