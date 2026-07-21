# Direction 1: Discovering New Ansatze Beyond Known Families

## Problem Statement

Five evolution campaigns (550+ MILP-verified iterations, three different model ensembles) all converge on the same three algebraic families:

- **Univariate (no constant term)**: A=y^a+y^b+y^c, B=x^d+x^e+x^f. High k (up to 160), but always d<=4 (MILP-verified).
- **x/y-swap**: A = x^a + y^b + y^c, B = y^d + x^e + x^f. Moderate k, high d. Best: Bravyi [[360,12,≤24]] FOM=19.2; our [[288,24,12]] FOM=12.0 (MILP exact).
- **Constant-monomial**: A = 1+y^a+y^b, B = 1+x^c+x^d. Technically also univariate (A=f(y), B=g(x)), but the constant term 1=x^0y^0 adds the identity matrix to each block, fundamentally changing kernel structure. Very high k, moderate d. Best: [[360,40,<=20]] FOM=44.4.

All three families share a key property: **every term in every polynomial is either pure-x or pure-y** (i.e., each monomial has the form x^a or y^b, never x^a*y^b with both a,b > 0). This means the parity check matrices decompose as sums of single-factor operators: each pure monomial x^a maps to I_m ⊗ P_ℓ^a (acts only on the x-cyclic factor) and y^b maps to P_m^b ⊗ I_ℓ (acts only on the y-cyclic factor). The two cyclic dimensions are never coupled within a single term.

**Mixed monomials** (terms like x^2*y^3) map to P_m^3 ⊗ P_ℓ^2 -- they act on **both** factors simultaneously, creating **diagonal shifts** on the ell x m torus. This couples the two cyclic dimensions and creates fundamentally different Tanner graph connectivity. This entire region of the search space is unexplored:

1. **Pattern lock-in**: The seed (`evolve/seed_solution.py:226-301`) has 4 strategies, all generating pure-variable terms only. Perturbations at line 254-269 do leak some mixed monomials (e.g., perturbing (3,0) y-coord → (3,1)), but only as incidental 1-step neighbors of pure-term codes -- never as deliberate constructions.
2. **Prompt lock-in**: `evolve/prompt_context.md:49` describes the x/y-swap pattern as "one pure-x term + two pure-y terms" and the entire strategies section guides toward pure-variable constructions.
3. **Term count lock**: `validate_terms()` at `evaluation/bb_code.py:60` enforces exactly 3 terms. This is a secondary constraint -- mixed-monomial trinomials are already a huge unexplored space -- but 4-6 term polynomials add another dimension to explore.

## Goal

Discover new structural families (ansatze) for BB codes by exploring the **mixed-monomial** region of the polynomial space. An ansatz is not a single code but a structural template -- an algebraic relationship between A and B that produces good codes across lattice sizes.

The campaign has two stages:

1. **Exploration**: Broad evolutionary search over mixed-monomial polynomials (and optionally 4-6 terms) to find codes with d >= 4 and interesting n/k/d tradeoffs.
2. **Pattern extraction**: Analyze the exploration results to identify structural motifs -- repeated algebraic relationships that correlate with high k or high d -- and abstract them into candidate ansatze.

### What makes this different from "just expand the search space"

The key scientific question is: **does breaking axis-aligned polynomial structure access new (k, d) tradeoffs?**

In x/y-swap codes, A = x^a + y^b + y^c is a sum of single-factor operators (I⊗P^a + P^b⊗I + P^c⊗I). The resulting matrix acts on the x and y cyclic factors independently -- each term shifts along one axis only. This factored structure is likely WHY x/y-swap gives high k -- the kernel inherits the tensor-product decomposition of the underlying group algebra.

Mixed monomials like x^2*y^3 create diagonal shifts -- they couple the x and y dimensions. This could:
- **Destroy k** (the high-k property depends on axis-aligned decomposition)
- **Destroy d** (diagonal shifts create different cycle structure in the Tanner graph)
- **OR unlock new tradeoffs** where different k values or different d values become accessible

Any of these outcomes is scientifically interesting. The campaign produces value regardless of whether FOM improves.

## Technical Approach

### Phase A: Core Infrastructure (low-risk, backward-compatible)

These changes apply to ALL campaigns and unlock the expanded search space.

#### A1. Generalize `validate_terms()` in `evaluation/bb_code.py`

Current code at line 60:

```python
if len(terms) != 3:
    raise ValueError(f"{name} must have exactly 3 terms, got {len(terms)}")
```

Change to:

```python
def validate_terms(
    ell: int, m: int, terms: list[tuple[int, int]], name: str = "polynomial",
    min_terms: int = 2, max_terms: int = 6,
) -> None:
    if not (min_terms <= len(terms) <= max_terms):
        raise ValueError(
            f"{name} must have {min_terms}-{max_terms} terms, got {len(terms)}"
        )
    # ... rest unchanged (reduced set, exponent range, duplicate checks)
```

Call sites all use positional args `(ell, m, terms, name)` -- new kwargs default harmlessly:

| File | Lines | Notes |
|------|-------|-------|
| `evaluation/evaluator.py` | 146-147 | `evaluate_candidate()` |
| `evaluation/evaluator.py` | 358-359 | `evaluate_candidate_milp()` |
| `tests/ablation_extended.py` | 46-47 | |
| `tests/ablation_k_only.py` | 67-68 | |
| `tests/verify_ga_distances.py` | import only | |

No downstream changes: `terms_to_poly()` (line 35) and `build_bb_code()` (line 81) already iterate over arbitrary-length term lists.

This is a **secondary** unlock -- mixed-monomial trinomials are the primary axis. But term count expansion is cheap and adds another dimension to explore.

#### A2. Fix test expectations in `tests/test_known_codes.py`

Line 72-73 asserts 2-term polynomials raise `ValueError`. With the new range [2, 6], update:
- Replace `test_wrong_count` with `test_too_few_terms` (1 term) and `test_too_many_terms` (7 terms)
- Add positive tests: `test_valid_2term`, `test_valid_4term`, `test_valid_5term` (with BBCode construction)

#### A3. Self-dual hard gate in both evaluators

All BB codes with A=B have d=2 exactly (Theorem 1, paper Sec III.D). BP-OSD misses this in 29/30 batches. Add to `evaluate_candidate()` (after line 173) and `evaluate_candidate_milp()` (after line 378):

```python
if sorted(tuple(t) for t in A_terms) == sorted(tuple(t) for t in B_terms):
    result["d"] = 2
    result["d_is_exact"] = True
    result["fom"] = k * 4 / n
    result["stage"] = "self_dual_d2"
    result["score"] = result["fom"]
    return result
```

Saves all distance computation on known-bad codes. Applies to all campaigns.

### Phase B: Exploration Campaign

#### B1. New seed: `evolve/seed_solution_ansatz.py`

The seed must CENTER mixed-monomial construction, not treat it as a side strategy. Design:

1. **Strategy 1 (primary): Mixed-monomial trinomials** -- deliberate construction of polynomials where A and B both contain terms with nonzero x AND y exponents. This is the main thing we're exploring.
2. **Strategy 2: Extend known codes to 4 terms** -- add a mixed monomial x^a*y^b to reference trinomials. Tests whether breaking the pure-term structure of known good codes helps or hurts.
3. **Strategy 3: Perturbations** -- standard perturbation of reference codes as fallback.

**Safety net (outside EVOLVE-BLOCK)**: Known pure-term codes are included via `_safety_net_codes()`, defined outside the EVOLVE-BLOCK markers. This is critical — the system message tells the LLM to "AVOID all pure-term constructions," so if the safety net were inside the evolvable code, the LLM would be incentivized to delete it. Placing it outside ensures the cascade always has k > 0 fallback codes at stage 1 lattices, regardless of what the LLM does to Strategies 1-3.

**Critical cascade constraint**: `evaluate_stage1` requires valid codes at ALL of `STAGE1_LATTICES = [(6,6), (12,6)]`. The safety net guarantees k > 0 at both lattices. The LLM then focuses on discovering which mixed-monomial structures ALSO produce k > 0.

```python
REFERENCE_CODES = [
    # Required for stage 1 — (6,6) must have a working fallback
    {"ell": 6, "m": 6,
     "A": [(3, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (1, 0), (2, 0)]},
    {"ell": 12, "m": 6,
     "A": [(3, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (1, 0), (2, 0)]},
    {"ell": 24, "m": 6,
     "A": [(6, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (2, 0), (4, 0)]},
    {"ell": 12, "m": 12,
     "A": [(6, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (2, 0), (4, 0)]},
]


def _safety_net_codes(ell, m):
    """Always include known pure-term codes to keep cascade alive.

    OUTSIDE EVOLVE-BLOCK — the LLM cannot remove these. Without them,
    if all mixed-monomial codes have k=0, the cascade threshold (0.01) is
    never met, stage 2 never runs, and the LLM never gets distance feedback.
    """
    codes = []
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            codes.append((list(ref["A"]), list(ref["B"])))
    return codes


# EVOLVE-BLOCK-START
def generate_candidates(ell, m):
    # Start with safety-net codes (defined outside this block, non-removable)
    candidates = list(_safety_net_codes(ell, m))
    seen = {(tuple(sorted(a)), tuple(sorted(b))) for a, b in candidates}

    def _add(a_terms, b_terms):
        # Reject self-dual (always d=2)
        if sorted(a_terms) == sorted(b_terms):
            return
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    # Strategy 1: Constant + mixed-monomial trinomials
    # A = 1 + (mixed) + (mixed or pure), B = 1 + (mixed) + (transposed mixed)
    # The constant term (identity matrix) is included deliberately — it's known
    # to help k > 0 in the constant-monomial family. This lets us isolate the
    # effect of mixed monomials vs pure terms while keeping the identity anchor.
    # Note: general mixed trinomials WITHOUT constant term (e.g., x*y + x²y³ + x³y)
    # are not generated here — the LLM can explore those if Strategy 1 shows promise.
    for a1x in range(1, min(ell, 5)):
        for a1y in range(1, min(m, 5)):
            # A = 1 + x^a1*y^a2 + (pure or mixed third term)
            for a2x in range(0, min(ell, 5)):
                for a2y in range(0, min(m, 5)):
                    A = [(0, 0), (a1x, a1y), (a2x, a2y)]
                    if len(set(A)) != 3:
                        continue
                    # B: try complementary diagonal shifts
                    for b1x in range(1, min(ell, 5)):
                        for b1y in range(1, min(m, 5)):
                            # B = 1 + x^b1*y^b2 + x^b3*y^b4
                            B = [(0, 0), (b1x, b1y), (b1y, b1x)]
                            if len(set(B)) == 3:
                                _add(A, B)

    # Strategy 2: Extend reference codes with a mixed monomial
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            for ax in range(1, min(ell, 5)):
                for ay in range(1, min(m, 5)):
                    extra = (ax, ay)
                    if extra not in ref["A"]:
                        _add(ref["A"] + [extra], ref["B"])
                    if extra not in ref["B"]:
                        _add(ref["A"], ref["B"] + [extra])

    # Strategy 3: Perturbations of reference codes
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            for delta in [-2, -1, 1, 2]:
                for i in range(len(ref["A"])):
                    for coord in [0, 1]:
                        new_A = [list(t) for t in ref["A"]]
                        limit = ell if coord == 0 else m
                        new_A[i][coord] = (new_A[i][coord] + delta) % limit
                        new_A_t = [tuple(t) for t in new_A]
                        if len(set(new_A_t)) == len(new_A_t):
                            _add(new_A_t, ref["B"])

    return candidates
# EVOLVE-BLOCK-END
```

The safety net is **outside** the EVOLVE-BLOCK — the LLM cannot remove it. This resolves the tension between the system message ("AVOID all pure-term constructions") and the cascade's need for k > 0 fallback codes. The LLM evolves only Strategies 1-3 (all mixed-monomial focused), while the safety net silently ensures the cascade always passes.

The seed is deliberately suboptimal -- mostly mixed-monomial codes that may have low FOM. The LLM's job is to discover WHICH mixed-monomial structures produce k > 0 and d >= 4.

#### B2. New prompt: `evolve/prompt_context_ansatz.md`

The prompt must give the LLM algebraic reasoning tools, not just "try mixed monomials":

1. **What you're evolving** -- function returning candidate BB code polynomial pairs
2. **Mathematical background** -- BB codes over F_2[x,y]/(x^ell-1, y^m-1), FOM = kd^2/n
3. **The scientific question** (key section):
   - "Known good BB codes use axis-aligned shifts: each term is pure-x (x^a) or pure-y (y^b). The parity check matrix decomposes along the two cyclic dimensions."
   - "Mixed monomials (x^a*y^b) create diagonal shifts on the ell x m torus. This couples the two dimensions and creates fundamentally different Tanner graph connectivity."
   - "We want to know: does breaking axis-aligned structure access new (k, d) tradeoffs?"
4. **Algebraic relationships to explore** between A and B:
   - "Complementary diagonal shifts: if A shifts along direction (a,b), does B shifting along (b,a) or (-b,a) create good codes?"
   - "Coordinate transforms: B = A(x^s, y^t) for coprime s, t"
   - "Shared ideal structure: do A and B that generate related ideals in the quotient ring produce high k?"
   - "Orthogonal shifts: A and B shift along perpendicular directions on the torus"
5. **Known dead ends** (all pure-term — this campaign is about mixed monomials):
   - "Univariate codes without constant term (A=y^a+y^b+y^c, B=x^d+x^e+x^f): typically d<=4."
   - "Constant-monomial codes (A=1+y^a+y^b, B=1+x^c+x^d): already explored in previous campaigns."
   - "Self-dual codes (A=B): always d=2. Auto-blocked by the evaluator."
6. **Constraints** -- return type, exponent ranges, 2-6 terms per polynomial, keep candidates to 100-2000 per lattice
7. **Evaluator feedback** -- artifact interpretation guide

**Critical difference from existing prompts**: the prompt describes algebraic RELATIONSHIPS between A and B to explore, not specific coefficient patterns. The LLM should be thinking about structural templates (ansatze), not individual codes.

#### B3. New config: `evolve/config_ansatz.yaml`

```yaml
max_iterations: 300
diff_based_evolution: true
checkpoint_interval: 25

llm:
  api_base: "http://localhost:4000/v1"
  models:
    - name: "aws/claude-opus-4-6"
      weight: 0.33
      temperature: 1.0
    - name: "Azure/gpt-5.2-2025-12-11"
      weight: 0.33
      temperature: null
    - name: "gcp/gemini-3-pro-preview"
      weight: 0.33
      temperature: 1.0
  max_tokens: 16384
  timeout: 300
  retries: 4
  retry_delay: 10

prompt:
  system_message: |
    You are an expert in quantum error-correcting codes. You are improving a Python
    function `generate_candidates(ell, m)` that returns candidate bivariate bicycle
    (BB) code polynomial pairs for evaluation.

    CONTEXT: All known good BB codes use axis-aligned polynomial terms (pure x^a or
    pure y^b). Mixed monomials (x^a*y^b with both a,b > 0) create diagonal shifts
    on the ell x m torus and are almost entirely unexplored. We want to find which
    mixed-monomial structures produce codes with good n/k/d tradeoffs (d >= 4).

    Metric: FOM = k*d^2/n. Any code with d >= 4 is a useful data point.

    YOUR TASK: Improve the generation function to produce mixed-monomial polynomial
    pairs where A and/or B contain terms like x^a*y^b. Focus on:
    - Structural relationships between A and B (complementary shifts, coordinate
      transforms, orthogonal shift directions)
    - Patterns that produce k > 0 at multiple lattice sizes (not one-off codes)
    - Combinations of axis-aligned and diagonal terms (2-6 terms per polynomial)

    AVOID (all pure-term constructions — this campaign explores MIXED monomials):
    - Univariate codes (A=f(y), B=g(x), no mixed terms): typically d<=4
    - Constant-monomial codes (A=1+y^a+y^b, B=1+x^c+x^d): already explored
    - Self-dual codes (A=B): always d=2 (auto-blocked by evaluator)

    When the evaluation reports a code with d >= 4, study its A and B terms in the
    feedback artifacts. What structural relationship made it work? Encode that
    relationship as a generation strategy that works across lattice sizes.
  include_artifacts: true
  suggest_simplification_after_chars: 10000

evaluator:
  timeout: 1200
  cascade_evaluation: true
  cascade_thresholds: [0.01, 0.5]
  parallel_evaluations: 6

database:
  population_size: 500
  num_islands: 5
  migration_interval: 20
  feature_dimensions: ["num_mixed_terms", "pattern_type"]
```

#### B4. Structured feedback in evaluator artifacts

Add to `evolve/openevolve_evaluator.py`:

**Pattern classifier** for MAP-Elites niche separation:

```python
def _classify_pattern(A_terms, B_terms) -> float:
    """Classify polynomial structure for MAP-Elites.

    0.0 = univariate, 1.0 = x/y-swap (pure terms, not univariate),
    2.0 = self-dual, 3.0 = novel (has mixed monomials)
    """
    a_set = sorted(tuple(t) for t in A_terms)
    b_set = sorted(tuple(t) for t in B_terms)
    if a_set == b_set:
        return 2.0
    a_y_only = all(x == 0 for x, y in A_terms)
    a_x_only = all(y == 0 for x, y in A_terms)
    b_y_only = all(x == 0 for x, y in B_terms)
    b_x_only = all(y == 0 for x, y in B_terms)
    if (a_y_only and b_x_only) or (a_x_only and b_y_only):
        return 0.0
    if not any(x > 0 and y > 0 for x, y in A_terms) and \
       not any(x > 0 and y > 0 for x, y in B_terms):
        return 1.0
    return 3.0
```

**Structural feedback** in stage 2 artifacts -- for each code with d >= 4, report simple structural properties that help the LLM reason about WHY a code worked:

- **Mixed vs pure term counts**: e.g., "A: 1 pure-x, 0 pure-y, 2 mixed. B: 0 pure-x, 1 pure-y, 2 mixed"
- **Shift direction vectors**: list the (dx, dy) displacements for each term, e.g., "A shifts: (3,0), (1,2), (0,4). B shifts: (0,3), (2,1), (4,0)"
- **Term count**: number of terms in A and B
- **Axis coupling**: "both A and B have mixed terms" vs "only A has mixed terms"

These are trivially computable (no algebraic machinery) and give the LLM structural vocabulary. More expensive analyses (GCD in the quotient ring, coordinate transform equivalence) belong in Phase D's post-campaign script, not in real-time evolution feedback.

### Phase C: BP-OSD Exploration

**Use BP-OSD for evolution.** Rationale:
- Exploratory campaign -- most codes will be bad, fast iteration matters
- BP-OSD: ~5s/code. MILP: ~2-5 min/code. 15x more iterations/hour.
- Trust filter (d/sqrt(n) <= 1.3) handles BP-OSD overestimates
- MILP verification happens post-hoc in Phase E

**Code logging for Phase D**: The evaluator currently only persists codes to `discovered_codes.json` when FOM > 6.0 (`openevolve_evaluator.py:503`). This discards exactly the data Phase D needs — mixed-monomial codes with d=4-5 and modest k (e.g., k=4, d=4, n=144 → FOM=0.44). Add a lightweight JSONL logger in `_run_evaluation()` that appends ALL codes with d > 0 to `results/evolution/<run_name>/all_codes.jsonl` (run-specific to avoid mixing pilot and campaign data). Each line: `{ell, m, A_terms, B_terms, n, k, d, fom, pattern_type}`. This is ~200 bytes per code and provides the full dataset for pattern extraction.

### Phase D: Pattern Extraction (post-campaign analysis)

This is the step that turns exploration results into ansatz candidates. Missing from all previous plans. It has automated and manual components -- abstracting a structural template from specific codes requires human algebraic intuition.

Create `tests/analyze_ansatz_patterns.py`:

**Step 1: Automated property computation**

Load all codes with d >= 4 from `results/evolution/<run_name>/all_codes.jsonl` (the full code log from Phase C — includes codes below the FOM > 6.0 save threshold in `discovered_codes.json`) and compute:
- Number of mixed vs pure terms in A and B
- Term count per polynomial
- Shift direction vectors: {(a,b) for (a,b) in terms}
- **Full automorphism equivalence check**: does the code reduce to a known pure-term code under any automorphism of Z_ℓ × Z_m? For gcd(ℓ,m) = 1, only diagonal automorphisms exist (x→x^s, y→y^t; φ(ℓ)×φ(m) checks). For gcd(ℓ,m) > 1, non-diagonal automorphisms like y→x^k·y can map mixed to pure — check the full Aut(Z_ℓ × Z_m). Size varies (e.g., |Aut(Z_6×Z_6)| = |GL₂(Z_6)| ≈ 288) but is always computationally feasible. Also check B = φ(A) for all automorphisms φ (A-B relationship).
- Newton polytope: convex hull of exponent pairs for each polynomial
- Whether A or B factors as a product of simpler polynomials over F_2 (univariate factoring only -- full multivariate GCD in the quotient ring is a separate research problem)

**Step 2: Automated report generation**

Group codes by structural properties and generate a summary table:
- Group by (num_mixed_A, num_mixed_B, term_count_A, term_count_B)
- Within each group: range of k, range of d, lattice sizes covered
- Flag groups with d >= 4 at 2+ lattice sizes (candidate ansatz signals)
- Flag codes equivalent to known pure-term families under full Aut(Z_ℓ × Z_m)
- Flag B = φ(A) relationships for any automorphism φ

**Step 3: Human pattern recognition (manual)**

Review the report and identify candidate ansatze. This is the intellectually hard part -- looking at the top codes, spotting repeated algebraic motifs, and formulating a structural template. Examples of what to look for:
- "All codes in this group have B = A with x and y exponents swapped in each term" → conjugate ansatz
- "All codes have one axis-aligned term and two diagonal terms with perpendicular shift vectors" → orthogonal-diagonal ansatz
- "A and B are both evaluations of the same univariate polynomial at different points" → compositional ansatz

**Step 4: Automated generalization test**

For each candidate ansatz identified in Step 3:
- Parameterize the template (e.g., "A = 1 + x^a*y^b + x^c*y^d where a*d - b*c = ±1")
- Enumerate instances at lattice sizes NOT in the campaign
- Evaluate k (fast) and BP-OSD d for each instance
- If d >= 4 at 3+ new lattice sizes: confirmed ansatz

Output: "We found N candidate ansatze. Template X produces codes with k in [a,b] and d in [c,d] across M lattice sizes."

### Phase E: MILP Verification

Run MILP on two categories:
1. All codes with BP-OSD FOM > 8.0 from Phase C
2. Representative codes from each candidate ansatz identified in Phase D

Create `tests/verify_ansatz_codes.py`:
- MILP with 300s/logical, 7200s total (proven budget)
- Save to `results/ansatz_verified.json`

**Note on MILP and hardware**: MILP parallelizes across logical operators and codes via ProcessPoolExecutor. More cores help throughput (~5x on 64-core vs 14-core M4 Max), but the serial bottleneck is the hardest single logical per code (up to 300s). For batch verification of ~50 codes, a cloud instance is worthwhile.

## Implementation Checklist

### Phase A: Core Infrastructure (~1 hour)
1. [ ] `evaluation/bb_code.py`: generalize `validate_terms()` -- add `min_terms`/`max_terms` kwargs, update docstring
2. [ ] `tests/test_known_codes.py`: replace `test_wrong_count` with boundary tests; add 4-term/5-term positive tests
3. [ ] `evaluation/evaluator.py`: add self-dual hard gate in `evaluate_candidate()` after line 173
4. [ ] `evaluation/evaluator.py`: add self-dual hard gate in `evaluate_candidate_milp()` after line 378
5. [ ] Run: `uv run python -m pytest tests/ -v` -- all tests pass

### Phase B: Exploration Campaign Setup (~2-3 hours)
6. [ ] Create `evolve/seed_solution_ansatz.py` -- mixed-monomial-first seed with stage 1 safety net
7. [ ] Create `evolve/prompt_context_ansatz.md` -- relationship-oriented prompt with algebraic reasoning tools
8. [ ] Create `evolve/config_ansatz.yaml` -- temperature 1.0, num_mixed_terms + pattern_type features
9. [ ] `evolve/openevolve_evaluator.py`: add `_classify_pattern()` and simple structural feedback in artifacts (mixed/pure counts, shift vectors)
10. [ ] `evolve/openevolve_evaluator.py`: add JSONL logger for ALL codes with d > 0 (for Phase D analysis)
11. [ ] Wire `pattern_type` and `num_mixed_terms` into `_run_evaluation()` and both stage functions
12. [ ] Test: mixed-monomial trinomials produce valid BBCodes with correct n, k
13. [ ] Test: 4-term and 5-term polynomials produce valid BBCodes
14. [ ] Test: `_classify_pattern` labels known codes correctly
15. [ ] Test: self-dual gate returns d=2 for A=B, does NOT fire for A!=B
16. [ ] Test: seed produces k > 0 codes at BOTH stage 1 lattices (6,6) and (12,6)
17. [ ] **Go/no-go diagnostic**: run Strategy 1 alone at (6,6) and (12,6), compute k for all outputs. Report k > 0 rate. If 0%, the LLM has no mixed-monomial signal to learn from — restructure before proceeding (e.g., try constant+mixed 4-term codes, or test different lattice sizes for Strategy 1)
18. [ ] Dry run: 1 iteration with the new seed/config

### Phase C: BP-OSD Exploration (~4-24 hours)
19. [ ] Pilot: 50 iterations with BP-OSD
20. [ ] Review: pattern distribution, any mixed-monomial codes with d >= 4?
21. [ ] If promising: full campaign (300 iterations)

### Phase D: Pattern Extraction
22. [ ] `tests/analyze_ansatz_patterns.py`: automated property computation + report generation (Steps 1-2)
23. [ ] Manual review: inspect report, identify candidate structural templates (Step 3)
24. [ ] `tests/analyze_ansatz_patterns.py --generalize`: test candidate ansatze at held-out lattices (Step 4)

### Phase E: MILP Verification
25. [ ] MILP verify representative codes from each confirmed ansatz

## Risk Assessment

**Medium risk, moderate reward.**

### Risks

1. **Mixed monomials destroy k**: The high-k property of x/y-swap codes likely depends on axis-aligned decomposition. Breaking this may systematically reduce k, making it impossible to achieve competitive FOM. This is the primary risk. In the worst case, most mixed-monomial codes have k=0 and the campaign produces little data. Mitigated by the safety net outside the EVOLVE-BLOCK (ensures cascade always passes) and by the fact that k=0 itself is informative — it means the axis-aligned structure IS necessary for nontrivial kernel.

2. **Trivial equivalence (real risk at most lattices)**: The automorphism group of the group algebra F_2[Z_ℓ × Z_m] depends on gcd(ℓ,m). When **gcd(ℓ,m) = 1** (only (9,8) and (16,9) in our lattices), the automorphisms are diagonal: x→x^s, y→y^t. Under these, mixed stays mixed — the structure IS an invariant. But when **gcd(ℓ,m) > 1** (most of our lattices: (6,6), (12,6), (24,6), (12,12), (15,12), etc.), non-diagonal automorphisms exist that mix the x and y factors. Example: at (6,6), the map y→x·y, x→x sends the pure-y polynomial 1+y+y² to the mixed polynomial 1+xy+x²y². So a "novel mixed-monomial" code could be a known pure-term code in disguise. Not ALL mixed-monomial codes reduce this way — only those where exponent relationships match the automorphism's shift pattern. Phase D must check the full Aut(Z_ℓ × Z_m), not just diagonal automorphisms, to deduplicate before claiming novelty.

3. **Search space explosion**: Mixed-monomial trinomials at (12,12): O(144^3) ~ 3M candidates vs O(24^3) ~ 14K for pure-term trinomials. 200x larger. The seed must sample structured subsets, not enumerate.

4. **No ansatz emerges**: The exploration finds scattered good codes but no repeating structural pattern. Mitigated by the pattern extraction analysis (Phase D) which systematically looks for clusters.

5. **LLM gravitates to pure terms**: Even with mixed-monomial-first seed and relationship-oriented prompt, LLMs may find it easier to reason about pure-variable patterns. Mitigated by three mechanisms: (a) the EVOLVE-BLOCK contains zero pure-term strategies — there's nothing pure-term for the LLM to optimize; (b) the system message explicitly says "AVOID all pure-term constructions"; (c) MAP-Elites `pattern_type` niche ensures novel (mixed) codes maintain population share even if pure-term codes score higher.

### What we learn regardless

- **Does axis-aligned structure matter for k?** If mixed-monomial codes systematically have lower k, that tells us the tensor-product-like decomposition IS the mechanism for high k in BB codes.
- **Does diagonal connectivity help d?** If mixed monomials can achieve d >= 6, that's a new construction technique.
- **Tradeoff frontier**: For mixed-monomial codes, what (k, d) pairs are achievable at each n?
- **Ansatz or no ansatz**: Either we find a new template (publishable), or we establish that mixed monomials don't form productive families (also publishable -- it would explain why the literature only uses pure-variable terms).

## Success Criteria

| Tier | Criterion | Likelihood |
|------|-----------|------------|
| 1 (ambitious) | New ansatz: a structural template with d >= 6 that generalizes across 3+ lattice sizes | Low (~15%) |
| 2 (valuable) | Mixed-monomial code with d >= 6 and k >= 8 at any lattice (proves the structure can work) | Medium (~30%) |
| 3 (informative) | Systematic data: how does mixed-monomial structure affect k and d compared to pure-term? | High (~80%) |

Even Tier 3 justifies the campaign. Understanding WHY the literature uses only pure-variable terms -- whether it's optimal or accidental -- is a publishable finding.

## Launch Commands

Pilot (50 iterations, ~4 hours):
```bash
uv run python evolve/run_evolution.py \
  --config evolve/config_ansatz.yaml \
  --seed evolve/seed_solution_ansatz.py \
  --iterations 50 \
  --run-name ansatz_pilot_v1
```

Full campaign (300 iterations, ~24 hours):
```bash
uv run python evolve/run_evolution.py \
  --config evolve/config_ansatz.yaml \
  --seed evolve/seed_solution_ansatz.py \
  --iterations 300 \
  --run-name ansatz_campaign4 \
  --wandb
```

Pattern analysis:
```bash
uv run python tests/analyze_ansatz_patterns.py \
  --codes results/evolution/ansatz_campaign4/all_codes.jsonl \
  --min-d 4
```

MILP verification:
```bash
uv run python tests/verify_ansatz_codes.py \
  --codes results/evolution/ansatz_campaign4/all_codes.jsonl \
  --min-fom 8.0
```
