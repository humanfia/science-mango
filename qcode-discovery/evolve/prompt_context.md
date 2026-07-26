# Bivariate Bicycle Code Discovery — Domain Knowledge for LLM

## What You're Evolving

You are evolving a Python function `generate_candidates(ell, m)` that returns candidate bivariate bicycle (BB) quantum error-correcting codes. Each candidate is a pair of trinomials (A, B) represented as exponent lists.

## Mathematical Background

A BB code is defined over the ring F_2[x,y]/(x^ℓ - 1, y^m - 1) by two weight-3 polynomials:
- A(x,y) = x^{a1}·y^{a2} + x^{a3}·y^{a4} + x^{a5}·y^{a6}
- B(x,y) = x^{b1}·y^{b2} + x^{b3}·y^{b4} + x^{b5}·y^{b6}

Exponents satisfy: 0 ≤ x-exponents < ℓ, 0 ≤ y-exponents < m.

The code has parameters [[n, k, d]] where:
- n = 2·ℓ·m (physical qubits)
- k = number of logical qubits (depends on algebraic structure)
- d = code distance (minimum weight of nontrivial logical operator)

## Scoring

FOM = k·d²/n — higher is better. The target is FOM > 12.0.

## Known Best Codes

### Bravyi et al. 2024 (baseline)
| Code | ℓ | m | A_terms | B_terms | FOM |
|------|---|---|---------|---------|-----|
| [[72,12,6]] | 6 | 6 | [(3,0),(0,1),(0,2)] | [(0,3),(1,0),(2,0)] | 6.0 |
| [[90,8,10]] | 15 | 3 | [(9,0),(0,1),(0,2)] | [(0,0),(2,0),(7,0)] | 8.9 |
| [[144,12,12]] | 12 | 6 | [(3,0),(0,1),(0,2)] | [(0,3),(1,0),(2,0)] | 12.0 |
| [[288,12,18]] | 12 | 12 | [(3,0),(0,2),(0,7)] | [(0,3),(1,0),(2,0)] | 13.5 |
| [[360,12,≤24]] | 30 | 6 | [(9,0),(0,1),(0,2)] | [(0,3),(25,0),(26,0)] | 19.2 |

### Our verified discoveries (150k-trial multi-decoder protocol)
| Code | ℓ | m | A_terms | B_terms | FOM | Pattern |
|------|---|---|---------|---------|-----|---------|
| **[[360,40,≤20]]** | 15 | 12 | [(0,0),(0,1),(0,2)] | [(0,0),(5,0),(10,0)] | **44.4** | const-mono |
| **[[288,32,≤20]]** | 12 | 12 | [(3,0),(0,2),(0,10)] | [(0,6),(1,0),(11,0)] | **44.4** | x/y-swap |
| [[360,32,≤16]] | 15 | 12 | [(0,0),(0,2),(0,4)] | [(0,0),(3,0),(4,0)] | 22.8 | const-mono |
| [[288,32,≤12]] | 12 | 12 | [(0,0),(0,2),(0,4)] | [(0,0),(2,0),(4,0)] | 16.0 | const-mono |
| [[288,24,≤12]] | 24 | 6 | [(6,0),(0,1),(0,2)] | [(0,3),(2,0),(4,0)] | 12.0 | x/y-swap |

## Two High-Performing Patterns

### Pattern 1: x/y-swap (baseline)

Most Bravyi et al. codes follow this structure:
- **A = x^a + y^b + y^c** (one pure-x term + two pure-y terms)
- **B = y^d + x^e + x^f** (one pure-y term + two pure-x terms)

Observations:
1. **Doubling pattern**: In the gross code, A = x^3 + y + y^2 and B = y^3 + x + x^2. Note c = 2b and f = 2e.
2. **Same polynomials, different lattices**: A = x^3+y+y^2, B = y^3+x+x^2 produces good codes at (6,6), (9,6), (12,6), (6,12), (18,6), (24,6).
3. **Small exponents matter**: The x-exponent `a` in A and y-exponent `d` in B tend to be small (≤ ℓ/2).
4. **The [[288,12,18]] exception**: Uses y^2+y^7 instead of y+y^2 — non-consecutive y-exponents.
5. **The [[360,12,≤24]] pattern**: Uses x^9 and B has x^25+x^26 (adjacent exponents near ℓ=30).

### Pattern 2: Constant-monomial (discovered by evolution, highest FOM)

The best code found ([[360,40,≤20]], FOM=44.4) uses a different structure:
- **A = 1 + y^a + y^b** (univariate in y, includes constant term 1)
- **B = 1 + x^c + x^d** (univariate in x, includes constant term 1)

Key properties:
1. **Both polynomials are univariate with a constant term** — this generates circulant matrices with special kernel structure, producing very high k.
2. **Frobenius-square subfamily**: A = 1+y²+y⁴ = (1+y+y²)² over F₂. Achieves k=32 at n=144, 288. High k but low distance.
3. **Irreducible subfamily**: A = 1+y+y² (irreducible over F₂). Achieves k=40 at (15,12).
4. **Compositional relationship**: For the best code, B = 1+x⁵+x¹⁰ = A(x⁵) — the same irreducible trinomial evaluated at x⁵. Try B = A(x^c) for various c dividing ℓ.
5. **Algebraic condition**: For A = 1+y+y², need 3 | m for nontrivial kernel. For high k, also want 3 | ℓ.
6. **Trade-off**: Constant-monomial codes achieve very high k but lower d than x/y-swap codes at the same n. The advantage only overcomes the d penalty at larger n (≥288).

## Constraints on Your Function

- Must return `list[tuple[list[tuple[int,int]], list[tuple[int,int]]]]`
- Each inner list must have exactly 3 tuples (trinomials)
- x-exponents must be in [0, ell), y-exponents in [0, m)
- All 3 monomials in each polynomial must be distinct
- Keep total candidates manageable (~100-1000 per lattice)
- Use standard Python + numpy only

## Strategies to Explore

### Constant-monomial extensions (highest potential)
- **Compositional B = A(x^c)**: For A = 1+y+y², try B = 1+x^c+x^{2c} for each c dividing ℓ
- **Frobenius squares**: Try A = 1+y^{2a}+y^{4a} = (1+y^a+y^{2a})² for various a
- **New irreducible trinomials**: Try A = 1+y^a+y^b for other irreducible polynomials over F₂
- **Divisibility conditions**: For A = 1+y+y², ensure 3 | m and try lattices where 3 | ℓ for maximum k

### x/y-swap refinements
- **Vary the doubling pattern**: Instead of c=2b, try c=3b, c=b+1, c=m-b
- **Non-consecutive y-pairs**: Like [[288,12,18]] which uses y^2+y^7
- **Large x-exponent regime**: Like [[360,12,≤24]] which uses x^9 at ℓ=30
- **Perturbation of verified codes**: ±1, ±2 on each exponent of the k=32 codes

### General
- **Coprimality heuristics**: Choose `a` coprime to ℓ, `d` coprime to m
- **Divisor-based constructions**: Use divisors of ℓ and m as exponents
- **Symmetry breaking**: Try mixed monomials (x^a·y^b with both a,b > 0)
- **Hybrid patterns**: Combine constant-monomial A with x/y-swap B, or vice versa

## Evaluator Feedback

After each evaluation, you receive artifacts with structured feedback. Here's how to interpret them:

### Metrics

| Metric | Meaning | What to optimize |
|--------|---------|-----------------|
| `combined_score` | Primary fitness: sum of best credible FOM per lattice (d/√n trust filter) | Maximize — this drives selection |
| `best_fom` | Highest FOM across all lattices | Target > 12.0 |
| `mean_fom` | Average FOM of valid codes | Higher means consistently good strategies |
| `num_valid` | Candidates with k > 0 | Higher is better — many k=0 means bad algebra |
| `num_above_6` | Codes with FOM ≥ 6.0 | Breadth of good codes |
| `num_above_12` | Codes with FOM ≥ 12.0 | Exceptional codes |
| `total_candidates` | Total generated | Keep in 100–1000 range per lattice |

### Artifacts

- **`best_code`**: The top code found, e.g. `[[144,12,12]] FOM=12.00 at (12,6)` with A and B terms. Use this to understand which polynomial patterns work.
- **`summary`**: Aggregate stats across all lattices evaluated.
- **`errors`**: Runtime errors from your function. Common issues:
  - `returned NoneType, not list` — forgot to return candidates
  - `candidates capped to 5000` — generating too many; focus on quality over quantity
  - `IndexError` / `TypeError` — bug in the generation logic

### Evaluation Stages

The evaluator uses a cascade to save time:

1. **Stage 1** (quick screening, ~2s): Runs on 2 small lattices `(6,6)` and `(12,6)` with k-only computation. Programs must produce at least some valid codes (k > 0) to advance.
2. **Stage 2** (full evaluation, ~30-60s): Runs on 8 lattices `(12,6), (6,12), (12,12), (24,6), (15,12), (30,6), (16,9), (18,8)` with distance estimation via BP-OSD (1000 trials OSD_0 + 200 trials OSD-CS order 10 for top candidates). Distance estimates are filtered by d/√n ratio — only codes with d ≤ 1.3·√n are fully trusted.

### Tips for Improving Score

1. **If num_valid is low**: Your candidates have poor algebraic structure. Try the x/y-swap pattern more consistently.
2. **If best_fom is stuck below 6**: You're finding codes with decent k but low d. Try larger exponents or non-trivial patterns.
3. **If you're generating 5000+ candidates**: Focus on fewer, higher-quality candidates. Use mathematical heuristics to prune.
4. **If errors mention specific lattices**: Some lattice sizes are harder. The same polynomial may work at (12,6) but not (10,10).
5. **To push FOM above 12**: Study the [[288,12,18]] and [[360,12,≤24]] patterns. Non-obvious exponent choices beat brute-force.
