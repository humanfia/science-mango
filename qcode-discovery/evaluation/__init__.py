"""Evaluation pipeline for bivariate bicycle quantum LDPC codes.

This package implements the full evaluation cascade that takes a candidate
polynomial pair ``(A_terms, B_terms)`` and produces code parameters
``[[n, k, d]]`` along with a figure of merit ``FOM = k * d^2 / n``.

Modules
-------
bb_code
    BB code construction -- converts exponent tuples to ``qldpc.BBCode``
    objects and provides fast ``(n, k)`` extraction.
distance
    Distance estimation -- BP-OSD upper bounds (OSD_0 and OSD-CS order 10)
    and exact brute-force distance with timeout.
evaluator
    Multi-stage evaluation cascade -- the central ``evaluate_candidate()``
    function that orchestrates validation, k computation, and progressive
    distance refinement.
results
    JSON persistence -- discovered codes file and Pareto front tracking.
tracking
    Run logging -- structured JSONL files for per-evaluation and
    per-generation metrics, plus run metadata.
"""
