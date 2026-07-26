#!/usr/bin/env python3
"""GA on generator functions: the gold-standard control for LLM contribution.

This experiment tests whether a classical genetic algorithm operating on the
SAME generator-function representation (Python programs) as the LLM can match
Campaign 1's results. This isolates the LLM contribution from the program-level
representation effect.

Architecture:
- Genome: Python source code of generate_candidates() function
  (exact same representation as OpenEvolve's EVOLVE-BLOCK)
- Mutation: programmatic (integer literal changes, strategy block operations)
- Crossover: strategy block recombination between parent programs
- Selection: tournament selection with elitism
- Evaluation: same Σk metric across Stage 2 lattices, with Stage 1 gating
- Budget: equal-budget (100 evals = Campaign 1) + extended (3000+ evals)

The seed is the EXACT generate_candidates() from evolve/seed_solution.py.
KNOWN_CODES is passed via exec namespace, matching OpenEvolve's setup.

Usage::

    uv run python tests/ablation_ga_generators.py
    uv run python tests/ablation_ga_generators.py --seeds 5 --pop-size 100 --generations 30
    uv run python tests/ablation_ga_generators.py --quick  # 1 seed, pop=20, 10 gens
"""

from __future__ import annotations

import argparse
import json
import re
import random as rng
import sys
import textwrap
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evolve.seed_solution import KNOWN_CODES

# ── Lattices (same as openevolve_evaluator.py) ────────────────────

STAGE1_LATTICES = [(6, 6), (12, 6)]

STAGE2_LATTICES = [
    (12, 6), (6, 12),
    (12, 12), (24, 6),
    (15, 12), (30, 6),
    (16, 9), (18, 8),
]

# ── Seed: exact EVOLVE-BLOCK from seed_solution.py ───────────────

SEED_SOURCE = textwrap.dedent('''\
def generate_candidates(ell, m):
    candidates = []
    seen = set()

    def _add(a_terms, b_terms):
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    # Strategy 1: x/y-swap symmetric construction
    max_a = ell // 2 + 1
    max_y = m // 2 + 1
    for a in range(1, max_a):
        for b in range(1, max_y):
            c = (2 * b) % m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) != 3:
                continue
            for d in range(1, max_y):
                for e in range(1, max_a):
                    f = (2 * e) % ell
                    B = [(0, d), (e, 0), (f, 0)]
                    if len(set(B)) == 3:
                        _add(A, B)

    # Strategy 2: Perturbations of known good codes at this lattice
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            base_A = code_spec["A_terms"]
            base_B = code_spec["B_terms"]
            _add(base_A, base_B)

            for delta in [-2, -1, 1, 2]:
                for i in range(3):
                    for coord in [0, 1]:
                        new_A = [list(t) for t in base_A]
                        limit = ell if coord == 0 else m
                        new_A[i][coord] = (new_A[i][coord] + delta) % limit
                        new_A_tuples = [tuple(t) for t in new_A]
                        if len(set(new_A_tuples)) == 3:
                            _add(new_A_tuples, base_B)

                        new_B = [list(t) for t in base_B]
                        limit = ell if coord == 0 else m
                        new_B[i][coord] = (new_B[i][coord] + delta) % limit
                        new_B_tuples = [tuple(t) for t in new_B]
                        if len(set(new_B_tuples)) == 3:
                            _add(base_A, new_B_tuples)

    # Strategy 3: Self-similar scaling
    canonical_polys = [
        ([(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
        ([(9, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ]
    for A, B in canonical_polys:
        if all(a < ell and b < m for a, b in A) and \\
           all(a < ell and b < m for a, b in B):
            _add(A, B)

    # Strategy 4: Full x/y-swap search
    max_x = min(ell, 5)
    max_yy = min(m, 5)
    for a in range(1, max_x):
        for b in range(0, max_yy):
            for c in range(b + 1, max_yy):
                A = [(a, 0), (0, b), (0, c)]
                if len(set(A)) != 3:
                    continue
                for d in range(1, max_yy):
                    for e in range(0, max_x):
                        for f in range(e + 1, max_x):
                            B = [(0, d), (e, 0), (f, 0)]
                            if len(set(B)) == 3:
                                _add(A, B)

    return candidates
''')

# ── Strategy templates for insertion mutations ────────────────────

STRATEGY_TEMPLATES = [
    textwrap.dedent('''\
    # Strategy: half-shift x/y-swap
    half_l = ell // 2
    half_m = m // 2
    for a in range(1, min(ell, 7)):
        for b in range(1, min(m, 7)):
            c = (b + half_m) % m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) != 3:
                continue
            for d in range(1, min(m, 7)):
                for e in range(1, min(ell, 7)):
                    f = (e + half_l) % ell
                    B = [(0, d), (e, 0), (f, 0)]
                    if len(set(B)) == 3:
                        _add(A, B)
    '''),
    textwrap.dedent('''\
    # Strategy: divisor-based exponents
    for div_l in range(2, min(ell, 8)):
        if ell % div_l != 0:
            continue
        for div_m in range(2, min(m, 8)):
            if m % div_m != 0:
                continue
            a = ell // div_l
            b = 1
            c = m // div_m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) == 3:
                B = [(0, c), (b, 0), (a, 0)]
                if len(set(B)) == 3:
                    _add(A, B)
    '''),
    textwrap.dedent('''\
    # Strategy: coprime exponent search
    from math import gcd
    for a in range(1, min(ell, 6)):
        for b in range(1, min(m, 6)):
            if gcd(a, ell) > 1 or gcd(b, m) > 1:
                continue
            c = (2 * b) % m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) != 3:
                continue
            for d in range(1, min(m, 6)):
                if gcd(d, m) > 1:
                    continue
                for e in range(1, min(ell, 6)):
                    if gcd(e, ell) > 1:
                        continue
                    f = (2 * e) % ell
                    B = [(0, d), (e, 0), (f, 0)]
                    if len(set(B)) == 3:
                        _add(A, B)
    '''),
    textwrap.dedent('''\
    # Strategy: power-of-2 exponents
    pows_l = [p for p in [1, 2, 4, 8] if p < ell]
    pows_m = [p for p in [1, 2, 4, 8] if p < m]
    for a in pows_l:
        for b in pows_m:
            for c in pows_m:
                if b == c:
                    continue
                A = [(a, 0), (0, b), (0, c)]
                if len(set(A)) != 3:
                    continue
                for d in pows_m:
                    for e in pows_l:
                        for f in pows_l:
                            if e == f:
                                continue
                            B = [(0, d), (e, 0), (f, 0)]
                            if len(set(B)) == 3:
                                _add(A, B)
    '''),
    textwrap.dedent('''\
    # Strategy: mixed monomials
    for a in range(1, min(ell, 5)):
        for b in range(1, min(m, 5)):
            for c in range(1, min(m, 5)):
                if b == c:
                    continue
                A = [(a, b), (0, c), (a, 0)]
                if len(set(A)) == 3:
                    for d in range(1, min(m, 5)):
                        for e in range(1, min(ell, 5)):
                            B = [(0, d), (e, 0), (e, b)]
                            if len(set(B)) == 3:
                                _add(A, B)
    '''),
    textwrap.dedent('''\
    # Strategy: tripling x/y-swap
    for a in range(1, min(ell, 6)):
        for b in range(1, min(m, 6)):
            c = (3 * b) % m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) != 3:
                continue
            for d in range(1, min(m, 6)):
                for e in range(1, min(ell, 6)):
                    f = (3 * e) % ell
                    B = [(0, d), (e, 0), (f, 0)]
                    if len(set(B)) == 3:
                        _add(A, B)
    '''),
]

# ── Fast k computation (direct numpy, no qldpc/sympy overhead) ───

# Global cache: avoids recomputing k for candidates seen across programs.
# Key insight: mutated programs generate heavily overlapping candidate sets.
_k_cache: dict[tuple, int] = {}


def _build_circulant(ell: int, m: int,
                     terms: list[tuple[int, int]]) -> np.ndarray:
    """Build ℓm × ℓm binary circulant matrix for polynomial terms."""
    n = ell * m
    mat = np.zeros((n, n), dtype=np.uint8)
    rows = np.arange(n)
    rx = rows // m
    ry = rows % m
    for ax, ay in terms:
        col_x = (rx + ax) % ell
        col_y = (ry + ay) % m
        cols = col_x * m + col_y
        mat[rows, cols] ^= 1
    return mat


def _gf2_rank(M: np.ndarray) -> int:
    """Compute rank of binary matrix over GF(2) via Gaussian elimination."""
    M = M.copy()
    nrows, ncols = M.shape
    rank = 0
    for col in range(ncols):
        # Find pivot in column (vectorized)
        col_vec = M[rank:, col]
        if not col_vec.any():
            continue
        pivot = rank + int(np.argmax(col_vec))
        # Swap pivot row with current rank row
        if pivot != rank:
            M[[rank, pivot]] = M[[pivot, rank]]
        # Eliminate all other rows with a 1 in this column
        mask = M[:, col].astype(bool)
        mask[rank] = False
        if mask.any():
            M[mask] ^= M[rank]
        rank += 1
        if rank == nrows:
            break
    return rank


def fast_compute_k(ell: int, m: int,
                   A_terms: list, B_terms: list) -> int:
    """Compute k for BB code directly via GF(2) rank, bypassing qldpc.

    Returns k >= 0 (0 on validation failure).
    """
    # Validate and reduce terms
    try:
        a_set = set()
        for ax, ay in A_terms:
            ax, ay = int(ax) % ell, int(ay) % m
            a_set.add((ax, ay))
        if len(a_set) < 2:
            return 0
        b_set = set()
        for bx, by in B_terms:
            bx, by = int(bx) % ell, int(by) % m
            b_set.add((bx, by))
        if len(b_set) < 2:
            return 0
    except (TypeError, ValueError):
        return 0

    A_frozen = tuple(sorted(a_set))
    B_frozen = tuple(sorted(b_set))

    # Check cache
    cache_key = (ell, m, A_frozen, B_frozen)
    cached = _k_cache.get(cache_key)
    if cached is not None:
        return cached

    n_half = ell * m
    A_mat = _build_circulant(ell, m, list(a_set))
    B_mat = _build_circulant(ell, m, list(b_set))

    # Hx = [A | B],  Hz = [B^T | A^T]
    Hx = np.hstack([A_mat, B_mat])
    Hz = np.hstack([B_mat.T, A_mat.T])

    rank_hx = _gf2_rank(Hx)
    rank_hz = _gf2_rank(Hz)

    k = max(0, 2 * n_half - rank_hx - rank_hz)
    _k_cache[cache_key] = k
    return k


# ── Program evaluation ────────────────────────────────────────────

def _eval_lattice(args):
    """Evaluate a program on a single lattice (for multiprocessing)."""
    source, ell, m, known_codes = args
    n = 2 * ell * m
    try:
        namespace = {"KNOWN_CODES": known_codes}
        exec(compile(source, "<evolved>", "exec"), namespace)
        gen_func = namespace.get("generate_candidates")
        if gen_func is None:
            return (f"({ell},{m})", {"n": n, "max_k": 0, "n_cand": 0,
                                     "error": "no generate_candidates"})

        t0 = time.time()
        candidates = gen_func(ell, m)
        gen_time = time.time() - t0

        if gen_time > 30.0:
            return (f"({ell},{m})", {"n": n, "max_k": 0, "n_cand": 0,
                                     "error": "gen timeout"})

        if not candidates or not isinstance(candidates, list):
            return (f"({ell},{m})", {"n": n, "max_k": 0, "n_cand": 0})

        # Cap candidates to prevent runaway programs
        cands = candidates[:5000]
        max_k = 0
        n_valid = 0
        for A_terms, B_terms in cands:
            k = fast_compute_k(ell, m, A_terms, B_terms)
            if k > 0:
                n_valid += 1
                if k > max_k:
                    max_k = k

        return (f"({ell},{m})", {
            "n": n, "max_k": max_k,
            "n_cand": len(candidates), "n_valid": n_valid,
        })
    except Exception as e:
        return (f"({ell},{m})", {"n": n, "max_k": 0, "n_cand": 0,
                                 "error": str(e)[:200]})


def evaluate_program(source: str, lattices: list[tuple[int, int]],
                     known_codes: list[dict],
                     time_budget: float = 60.0) -> dict:
    """Evaluate a generator program: compute Σk across lattices.

    Uses two-stage cascade: Stage 1 gates on (6,6)+(12,6) before full eval.
    Time budget prevents pathological programs from blocking the GA.
    """
    t_start = time.time()

    # Stage 1 gate: quick check on small lattices
    stage1_pass = True
    for ell, m in STAGE1_LATTICES:
        key, result = _eval_lattice((source, ell, m, known_codes))
        if result.get("max_k", 0) == 0 and result.get("error"):
            stage1_pass = False
            break

    if not stage1_pass:
        return {"sum_max_k": 0, "per_lattice": {}, "stage1_fail": True}

    # Stage 2: full evaluation on all lattices
    per_lattice = {}
    sum_max_k = 0

    for ell, m in lattices:
        if time.time() - t_start > time_budget:
            break
        key, result = _eval_lattice((source, ell, m, known_codes))
        per_lattice[key] = result
        sum_max_k += result.get("max_k", 0)

    return {"sum_max_k": sum_max_k, "per_lattice": per_lattice}


# ── Program-level mutation operators ──────────────────────────────

def _find_strategy_blocks(source: str) -> list[tuple[int, int]]:
    """Find strategy block boundaries (start_line, end_line) in source."""
    lines = source.split('\n')
    blocks = []
    current_start = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('# Strategy'):
            if current_start is not None:
                blocks.append((current_start, i - 1))
            current_start = i
        elif stripped == 'return candidates' and current_start is not None:
            blocks.append((current_start, i - 1))
            current_start = None
    return blocks


def mutate_integer(source: str) -> str:
    """Change a random integer literal (2-99) in the source."""
    # Find all integer literals via regex (word-bounded to avoid partial matches)
    pattern = re.compile(r'(?<![.\w])(\d+)(?![.\w])')
    matches = [(m.start(), m.end(), m.group())
               for m in pattern.finditer(source)
               if 2 <= int(m.group()) <= 99]
    if not matches:
        return source

    start, end, orig_str = rng.choice(matches)
    orig_val = int(orig_str)

    r = rng.random()
    if r < 0.25:
        new_val = orig_val + 1
    elif r < 0.50:
        new_val = max(1, orig_val - 1)
    elif r < 0.65:
        new_val = orig_val + 2
    elif r < 0.80:
        new_val = max(1, orig_val - 2)
    elif r < 0.90:
        new_val = max(1, orig_val * 2)
    else:
        new_val = rng.randint(1, max(orig_val * 2, 10))

    return source[:start] + str(new_val) + source[end:]


def mutate_loop_bound(source: str) -> str:
    """Change a loop bound (min(x, N))."""
    pattern = r'min\((ell|m),\s*(\d+)\)'
    matches = list(re.finditer(pattern, source))
    if not matches:
        return mutate_integer(source)
    match = rng.choice(matches)
    old_val = int(match.group(2))
    new_val = max(2, old_val + rng.choice([-2, -1, 1, 2, 3]))
    return source[:match.start(2)] + str(new_val) + source[match.end(2):]


def mutate_multiplier(source: str) -> str:
    """Change a multiplier in expressions like (N * b) % m."""
    pattern = r'\((\d+)\s*\*\s*\w+\)\s*%\s*\w+'
    matches = list(re.finditer(pattern, source))
    if not matches:
        return mutate_integer(source)
    match = rng.choice(matches)
    old_val = int(re.search(r'\((\d+)', match.group()).group(1))
    new_val = rng.choice([v for v in [2, 3, 4, 5, 6] if v != old_val] or [3])
    s = match.start()
    paren_pos = source.index('(', s)
    num_end = paren_pos + 1 + len(str(old_val))
    return source[:paren_pos + 1] + str(new_val) + source[num_end:]


def mutate_add_strategy(source: str) -> str:
    """Add a new strategy block from the template library."""
    template = rng.choice(STRATEGY_TEMPLATES)
    for _ in range(rng.randint(0, 3)):
        template = mutate_integer(template)
    return_idx = source.rfind('return candidates')
    if return_idx == -1:
        return source
    indented = textwrap.indent(template, '    ')
    return source[:return_idx] + indented + '\n    ' + source[return_idx:]


def mutate_remove_strategy(source: str) -> str:
    """Remove a random strategy block (keep at least one)."""
    blocks = _find_strategy_blocks(source)
    if len(blocks) <= 1:
        return mutate_integer(source)
    idx = rng.randint(0, len(blocks) - 1)
    start, end = blocks[idx]
    lines = source.split('\n')
    return '\n'.join(lines[:start] + lines[end + 1:])


def mutate_duplicate_strategy(source: str) -> str:
    """Duplicate a strategy block with modified constants."""
    blocks = _find_strategy_blocks(source)
    if not blocks:
        return mutate_integer(source)
    idx = rng.randint(0, len(blocks) - 1)
    start, end = blocks[idx]
    lines = source.split('\n')
    block_source = '\n'.join(lines[start:end + 1])
    for _ in range(rng.randint(1, 4)):
        block_source = mutate_integer(block_source)
    block_source = re.sub(r'# Strategy[^:]*:', '# Strategy (mutated):',
                          block_source, count=1)
    new_lines = lines[:end + 1] + [''] + block_source.split('\n') + lines[end + 1:]
    return '\n'.join(new_lines)


def mutate_program(source: str) -> str:
    """Apply a random mutation to the program source."""
    r = rng.random()
    if r < 0.35:
        return mutate_integer(source)
    elif r < 0.55:
        return mutate_loop_bound(source)
    elif r < 0.70:
        return mutate_multiplier(source)
    elif r < 0.80:
        return mutate_add_strategy(source)
    elif r < 0.90:
        return mutate_duplicate_strategy(source)
    else:
        return mutate_remove_strategy(source)


def crossover_programs(parent1: str, parent2: str) -> str:
    """Crossover: combine strategy blocks from both parents."""
    blocks1 = _find_strategy_blocks(parent1)
    blocks2 = _find_strategy_blocks(parent2)
    if not blocks1 or not blocks2:
        return parent1

    lines1 = parent1.split('\n')
    lines2 = parent2.split('\n')

    block_sources1 = ['\n'.join(lines1[s:e + 1]) for s, e in blocks1]
    block_sources2 = ['\n'.join(lines2[s:e + 1]) for s, e in blocks2]

    all_blocks = block_sources1 + block_sources2
    n_blocks = rng.randint(2, min(len(all_blocks), 6))
    selected = rng.sample(all_blocks, n_blocks)

    # Rebuild program with standard header
    header = (
        "def generate_candidates(ell, m):\n"
        "    candidates = []\n"
        "    seen = set()\n"
        "\n"
        "    def _add(a_terms, b_terms):\n"
        "        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))\n"
        "        if key not in seen:\n"
        "            seen.add(key)\n"
        "            candidates.append((list(a_terms), list(b_terms)))\n"
        "\n"
    )
    body = '\n\n'.join(selected)
    # Ensure body lines are indented at function level (4 spaces)
    body_lines = []
    for line in body.split('\n'):
        stripped = line.strip()
        if stripped:
            # Check if already at correct indentation
            if line.startswith('    '):
                body_lines.append(line)
            else:
                body_lines.append('    ' + stripped)
        else:
            body_lines.append('')

    return header + '\n'.join(body_lines) + '\n\n    return candidates\n'


def is_valid_program(source: str) -> bool:
    """Check if the program is syntactically valid."""
    try:
        compile(source, "<check>", "exec")
        return True
    except SyntaxError:
        return False


# ── GA main loop ──────────────────────────────────────────────────

def _eval_program_worker(args):
    """Worker function for parallel program evaluation (runs in subprocess)."""
    source, lattices, known_codes = args
    # Each worker has its own k_cache (populated as it evaluates)
    return evaluate_program(source, lattices, known_codes)


def run_ga_on_generators(
    seed: int,
    pop_size: int = 100,
    n_generations: int = 30,
    tournament_size: int = 5,
    mutation_rate: float = 0.8,
    crossover_rate: float = 0.3,
    n_mutations_per_individual: int = 3,
    n_workers: int = 1,
    verbose: bool = True,
) -> dict:
    """Run the GA on generator functions. Fitness = Σk across Stage 2 lattices.

    Args:
        n_workers: Number of parallel workers for within-generation evaluation.
            1 = sequential (best cache reuse), >1 = parallel (faster wall time).
    """
    rng.seed(seed)
    np.random.seed(seed)
    t_start = time.time()

    if verbose:
        print(f"\n{'=' * 60}")
        print(f"  GA on Generator Functions (seed={seed})")
        print(f"  Pop={pop_size}, Gens={n_generations}, Workers={n_workers}")
        print(f"{'=' * 60}")

    # Initialize population: seed + mutations of seed
    population = [SEED_SOURCE]
    for _ in range(pop_size - 1):
        prog = SEED_SOURCE
        for _ in range(rng.randint(1, n_mutations_per_individual)):
            prog = mutate_program(prog)
            if not is_valid_program(prog):
                prog = SEED_SOURCE
                break
        population.append(prog)

    # Track state
    fitnesses = []
    best_fitness = 0
    best_program = SEED_SOURCE
    best_per_lattice = {}
    total_evals = 0

    known_codes_for_eval = KNOWN_CODES

    if verbose:
        print(f"\n  Evaluating initial population ({pop_size} programs)...")
        t_init = time.time()

    if n_workers > 1:
        # Parallel evaluation of initial population
        work_items = [(prog, STAGE2_LATTICES, known_codes_for_eval)
                      for prog in population]
        with ProcessPoolExecutor(max_workers=n_workers) as pool:
            results = list(pool.map(_eval_program_worker, work_items))
        for i, result in enumerate(results):
            fitness = result["sum_max_k"]
            fitnesses.append(fitness)
            total_evals += 1
            if fitness > best_fitness:
                best_fitness = fitness
                best_program = population[i]
                best_per_lattice = result.get("per_lattice", {})
    else:
        for i, prog in enumerate(population):
            result = evaluate_program(prog, STAGE2_LATTICES, known_codes_for_eval)
            fitness = result["sum_max_k"]
            fitnesses.append(fitness)
            total_evals += 1

            if fitness > best_fitness:
                best_fitness = fitness
                best_program = prog
                best_per_lattice = result.get("per_lattice", {})

            if verbose and (i + 1) % max(1, pop_size // 5) == 0:
                elapsed = time.time() - t_init
                rate = (i + 1) / elapsed if elapsed > 0 else 0
                print(f"    {i + 1}/{pop_size} evaluated ({rate:.1f} prog/s), "
                      f"best Σk={best_fitness}")

    if verbose:
        init_time = time.time() - t_init
        print(f"  Initial pop done in {init_time:.1f}s, best Σk={best_fitness}")
        for lk in sorted(best_per_lattice.keys()):
            lv = best_per_lattice[lk]
            print(f"    {lk}: k={lv.get('max_k', 0)}, cands={lv.get('n_cand', 0)}")

    history = [{
        "gen": 0,
        "best_fitness": best_fitness,
        "mean_fitness": round(sum(fitnesses) / len(fitnesses), 1),
        "total_evals": total_evals,
    }]

    # Evolution loop
    for gen in range(1, n_generations + 1):
        t_gen = time.time()
        new_population = []
        new_fitnesses = []

        # Elitism: keep top 10%
        n_elite = max(2, pop_size // 10)
        elite_indices = sorted(range(len(population)),
                               key=lambda i: fitnesses[i], reverse=True)[:n_elite]
        for idx in elite_indices:
            new_population.append(population[idx])
            new_fitnesses.append(fitnesses[idx])

        # Generate all offspring first (selection + mutation is fast)
        offspring = []
        while len(offspring) < pop_size - n_elite:
            # Tournament selection
            t_idxs = rng.sample(range(len(population)),
                                min(tournament_size, len(population)))
            parent_idx = max(t_idxs, key=lambda i: fitnesses[i])
            parent = population[parent_idx]

            # Crossover
            if rng.random() < crossover_rate:
                t2 = rng.sample(range(len(population)),
                                min(tournament_size, len(population)))
                p2_idx = max(t2, key=lambda i: fitnesses[i])
                child = crossover_programs(parent, population[p2_idx])
            else:
                child = parent

            # Mutation (try up to 5 times to get valid syntax)
            if rng.random() < mutation_rate:
                for _ in range(5):
                    mutated = child
                    for _ in range(rng.randint(1, n_mutations_per_individual)):
                        mutated = mutate_program(mutated)
                    if is_valid_program(mutated):
                        child = mutated
                        break

            if not is_valid_program(child):
                child = parent

            offspring.append(child)

        # Evaluate all offspring (parallel or sequential)
        if n_workers > 1:
            work_items = [(prog, STAGE2_LATTICES, known_codes_for_eval)
                          for prog in offspring]
            with ProcessPoolExecutor(max_workers=n_workers) as pool:
                results = list(pool.map(_eval_program_worker, work_items))
            for i, result in enumerate(results):
                fitness = result["sum_max_k"]
                total_evals += 1
                new_population.append(offspring[i])
                new_fitnesses.append(fitness)

                if fitness > best_fitness:
                    best_fitness = fitness
                    best_program = offspring[i]
                    best_per_lattice = result.get("per_lattice", {})
                    if verbose:
                        print(f"  Gen {gen}: NEW BEST Σk={best_fitness}")
                        for lk in sorted(best_per_lattice.keys()):
                            lv = best_per_lattice[lk]
                            print(f"    {lk}: k={lv.get('max_k', 0)}")
        else:
            for child in offspring:
                result = evaluate_program(child, STAGE2_LATTICES, known_codes_for_eval)
                fitness = result["sum_max_k"]
                total_evals += 1

                new_population.append(child)
                new_fitnesses.append(fitness)

                if fitness > best_fitness:
                    best_fitness = fitness
                    best_program = child
                    best_per_lattice = result.get("per_lattice", {})
                    if verbose:
                        print(f"  Gen {gen}: NEW BEST Σk={best_fitness}")
                        for lk in sorted(best_per_lattice.keys()):
                            lv = best_per_lattice[lk]
                            print(f"    {lk}: k={lv.get('max_k', 0)}")

        population = new_population
        fitnesses = new_fitnesses

        gen_time = time.time() - t_gen
        mean_fit = sum(fitnesses) / len(fitnesses)

        history.append({
            "gen": gen,
            "best_fitness": best_fitness,
            "mean_fitness": round(mean_fit, 1),
            "total_evals": total_evals,
            "gen_time_s": round(gen_time, 1),
        })

        if verbose and gen % max(1, n_generations // 10) == 0:
            print(f"  Gen {gen}/{n_generations}: best={best_fitness}, "
                  f"mean={mean_fit:.1f}, evals={total_evals}, {gen_time:.1f}s")

    total_time = time.time() - t_start

    if verbose:
        print(f"\n  Final: best Σk={best_fitness}, {total_evals} evals, "
              f"{total_time:.0f}s ({total_time / 60:.1f} min)")
        for lk in sorted(best_per_lattice.keys()):
            lv = best_per_lattice[lk]
            print(f"    {lk} (n={lv.get('n', '?')}): k={lv.get('max_k', 0)}, "
                  f"cands={lv.get('n_cand', 0)}")

    return {
        "seed": seed,
        "pop_size": pop_size,
        "n_generations": n_generations,
        "total_evals": total_evals,
        "total_time_s": round(total_time, 1),
        "best_fitness": best_fitness,
        "best_per_lattice": best_per_lattice,
        "best_program": best_program,
        "history": history,
    }


# ── Main ──────────────────────────────────────────────────────────

def _run_seed(seed_val, **kw):
    """Run a single GA seed in a separate process (resets k_cache)."""
    global _k_cache
    _k_cache = {}
    return run_ga_on_generators(seed=seed_val, **kw)


def main():
    parser = argparse.ArgumentParser(
        description="GA on generator functions ablation")
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--pop-size", type=int, default=100)
    parser.add_argument("--generations", type=int, default=30)
    parser.add_argument("--tournament", type=int, default=5)
    parser.add_argument("--quick", action="store_true",
                        help="Quick test: 1 seed, pop=20, 10 gens")
    parser.add_argument("--validate", action="store_true",
                        help="Validate fast_compute_k against qldpc")
    parser.add_argument("--parallel-seeds", action="store_true",
                        help="Run all seeds in parallel (one process per seed)")
    parser.add_argument("--workers", type=int, default=1,
                        help="Parallel workers per seed for within-generation eval "
                             "(default: 1 = sequential, best cache reuse)")
    args = parser.parse_args()

    if args.quick:
        args.seeds = 1
        args.pop_size = 20
        args.generations = 10

    # Validate fast_compute_k if requested
    if args.validate:
        _validate_fast_k()
        return

    total_evals = args.pop_size * (args.generations + 1)
    print("GA on Generator Functions -- Ablation Experiment")
    print(f"Seeds: {args.seeds}, Pop: {args.pop_size}, Gens: {args.generations}")
    print(f"Total evals per seed: ~{total_evals:,}")
    if args.parallel_seeds:
        print(f"Running {args.seeds} seeds in PARALLEL")
    if args.workers > 1:
        print(f"Workers per seed: {args.workers} (within-generation parallelism)")

    # Evaluate the seed baseline
    print("\n--- Seed baseline ---")
    t0 = time.time()
    seed_result = evaluate_program(SEED_SOURCE, STAGE2_LATTICES, KNOWN_CODES)
    seed_time = time.time() - t0
    print(f"Seed Σk = {seed_result['sum_max_k']} ({seed_time:.1f}s)")
    for lk in sorted(seed_result["per_lattice"].keys()):
        lv = seed_result["per_lattice"][lk]
        print(f"  {lk} (n={lv.get('n', '?')}): k={lv.get('max_k', 0)}, "
              f"cands={lv.get('n_cand', 0)}")

    est_hours = total_evals * seed_time / len(STAGE2_LATTICES) / 3600
    parallel_note = "" if args.parallel_seeds else f" × {args.seeds} seeds"
    print(f"\nEstimated runtime: ~{est_hours:.1f} hours per seed"
          f"{parallel_note}")

    # Run GA with multiple seeds
    seeds_list = [42 + i * 100 for i in range(args.seeds)]
    ga_kwargs = dict(
        pop_size=args.pop_size,
        n_generations=args.generations,
        tournament_size=args.tournament,
        n_workers=args.workers,
    )

    if args.parallel_seeds and args.seeds > 1:
        # Each seed runs in a separate process (independent caches)
        with ProcessPoolExecutor(max_workers=args.seeds) as pool:
            futures = [
                pool.submit(_run_seed, s, **ga_kwargs)
                for s in seeds_list
            ]
            all_results = [f.result() for f in futures]
    else:
        all_results = []
        for s in seeds_list:
            all_results.append(run_ga_on_generators(seed=s, **ga_kwargs))

    all_sigma_k = [r["best_fitness"] for r in all_results]

    # Summary
    print(f"\n{'=' * 70}")
    print("SUMMARY: GA on Generator Functions")
    print(f"{'=' * 70}")
    print(f"Seed baseline Σk = {seed_result['sum_max_k']}")
    print(f"GA Σk across {args.seeds} seeds: {all_sigma_k}")
    mean_sk = sum(all_sigma_k) / len(all_sigma_k)
    std_sk = (sum((x - mean_sk) ** 2 for x in all_sigma_k) / len(all_sigma_k)) ** 0.5
    print(f"GA on generators Σk: {mean_sk:.0f} ± {std_sk:.0f}")
    print(f"Campaign 1 (LLM) Σk = 704")
    print(f"GA on exponent tuples Σk = 703 ± 142")

    # Per-lattice best across all seeds
    per_lattice_best = {}
    for result in all_results:
        for lk, lv in result["best_per_lattice"].items():
            mk = lv.get("max_k", 0)
            if lk not in per_lattice_best or mk > per_lattice_best[lk]:
                per_lattice_best[lk] = mk

    print("\nPer-lattice best k (across all seeds):")
    for lk in sorted(per_lattice_best.keys()):
        print(f"  {lk}: max_k = {per_lattice_best[lk]}")

    # Save results
    output = {
        "experiment": "GA on generator functions",
        "description": ("Classical GA operating on same program representation "
                        "as LLM (EVOLVE-BLOCK of generate_candidates)"),
        "seed_baseline": {
            k: v for k, v in seed_result.items()
        },
        "config": {
            "pop_size": args.pop_size,
            "n_generations": args.generations,
            "tournament_size": args.tournament,
            "n_seeds": args.seeds,
            "total_evals_per_seed": total_evals,
            "stage1_lattices": [list(l) for l in STAGE1_LATTICES],
            "stage2_lattices": [list(l) for l in STAGE2_LATTICES],
        },
        "comparison": {
            "campaign_1_sigma_k": 704,
            "ga_exponent_tuples_sigma_k": "703 ± 142",
            "ga_generators_sigma_k": f"{mean_sk:.0f} ± {std_sk:.0f}",
            "ga_generators_values": all_sigma_k,
        },
        "runs": [{k: v for k, v in r.items() if k != "best_program"}
                 for r in all_results],
        "per_lattice_best": per_lattice_best,
    }

    output_path = Path("results/ablation_ga_generators.json")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {output_path}")


def _validate_fast_k():
    """Validate fast_compute_k against qldpc on known codes."""
    from evaluation.bb_code import build_bb_code, get_code_params_fast

    print("Validating fast_compute_k against qldpc...")
    test_cases = [
        (6, 6, [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)], 12),
        (12, 6, [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)], 12),
        (15, 3, [(9, 0), (0, 1), (0, 2)], [(0, 0), (2, 0), (7, 0)], 8),
        (12, 12, [(3, 0), (0, 2), (0, 7)], [(0, 3), (1, 0), (2, 0)], 12),
        (15, 12, [(0, 0), (0, 1), (0, 2)], [(0, 0), (5, 0), (10, 0)], 40),
    ]

    all_ok = True
    for ell, m, A, B, expected_k in test_cases:
        fast_k = fast_compute_k(ell, m, A, B)
        code = build_bb_code(ell, m, A, B)
        _, qldpc_k = get_code_params_fast(code)
        status = "OK" if fast_k == qldpc_k == expected_k else "FAIL"
        if status == "FAIL":
            all_ok = False
        print(f"  ({ell},{m}): fast={fast_k}, qldpc={qldpc_k}, "
              f"expected={expected_k} [{status}]")

    # Timing comparison
    ell, m = 12, 6
    A = [(3, 0), (0, 1), (0, 2)]
    B = [(0, 3), (1, 0), (2, 0)]
    n_trials = 200

    t0 = time.time()
    for _ in range(n_trials):
        fast_compute_k(ell, m, A, B)
    fast_time = (time.time() - t0) / n_trials * 1000

    t0 = time.time()
    for _ in range(n_trials):
        code = build_bb_code(ell, m, A, B)
        get_code_params_fast(code)
    qldpc_time = (time.time() - t0) / n_trials * 1000

    print(f"\nTiming at ({ell},{m}): fast={fast_time:.2f}ms, "
          f"qldpc={qldpc_time:.2f}ms, speedup={qldpc_time / fast_time:.1f}x")
    print(f"Validation: {'PASSED' if all_ok else 'FAILED'}")


if __name__ == "__main__":
    main()
