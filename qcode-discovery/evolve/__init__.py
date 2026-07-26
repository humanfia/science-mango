"""LLM-guided evolutionary search for bivariate bicycle codes.

This package implements the evolutionary loop that discovers novel BB code
constructions.  Rather than evolving individual polynomial pairs, it
evolves the **strategy** -- a Python function ``generate_candidates(ell, m)``
that produces batches of candidate polynomials for evaluation.

The evolutionary loop is powered by `OpenEvolve
<https://github.com/codelion/openevolve>`_, which mutates the code between
``# EVOLVE-BLOCK-START`` and ``# EVOLVE-BLOCK-END`` markers in the seed
solution using LLM-generated diffs.

Modules
-------
seed_solution
    Seed program containing known benchmark codes (``KNOWN_CODES``),
    target lattice dimensions (``TARGET_LATTICES``), and the initial
    ``generate_candidates()`` function that OpenEvolve mutates.
openevolve_evaluator
    Adapter between OpenEvolve's ``evaluate(program_path)`` interface and
    the project's evaluation cascade.  Implements a two-stage cascade:
    stage 1 (quick k-only screening) gates stage 2 (full distance
    estimation with trust filtering).
run_evolution
    CLI entry point for launching evolutionary runs.  Handles LiteLLM
    proxy connection, model ensemble configuration, W&B integration, and
    checkpoint resume.
config.yaml
    OpenEvolve configuration: population size, island migration,
    MAP-Elites feature dimensions, LLM ensemble, and cascade thresholds.
prompt_context.md
    Domain knowledge document fed to the LLM during mutations -- describes
    BB code algebra, known patterns, and strategies to explore.
"""
