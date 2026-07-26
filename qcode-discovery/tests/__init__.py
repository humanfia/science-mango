"""Test suite for the qcode-discovery project.

Tests are organized into three files:

``test_known_codes.py`` (38 tests, ~2 s excluding slow markers)
    Unit and integration tests for the entire evaluation pipeline.
    Validates polynomial construction, input validation, code building,
    known code parameters (``n`` and ``k`` for all 14 benchmark codes),
    FOM computation, the evaluation cascade stages, batch evaluation,
    JSON persistence, Pareto front logic, seed solution generation, and
    the run tracker lifecycle.  Two tests are marked ``@pytest.mark.slow``
    (BP-OSD distance estimation).

``soak_test.py`` (CLI script, not pytest -- runtime: 30-120 min)
    Rigorous multi-decoder soak test for verifying distance upper bounds.
    Runs 3 decoder configurations x 10 batches x 5000 trials = 150,000
    total trials per code.  Produces a JSON report with per-decoder
    statistics, global min/max distances, trust assessment, and comparison
    against Bravyi et al. baselines.  This is the publication-quality
    verification protocol.

``verify_bravyi_codes.py`` (CLI script, not pytest -- runtime: ~30 min)
    Re-verifies Bravyi et al. (2024) baseline codes under the same
    150k-trial protocol, addressing the "asymmetric baseline comparison"
    concern from paper reviews.

Running tests::

    uv run python -m pytest tests/ -v              # all 38 tests (~2 s)
    uv run python -m pytest tests/ -v -m "not slow" # skip distance tests
    uv run python tests/soak_test.py               # soak test (slow)
    uv run python tests/verify_bravyi_codes.py     # baseline verification (slow)
"""
