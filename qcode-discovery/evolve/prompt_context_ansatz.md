# Novel Ansatz Discovery — Domain Knowledge for LLM

## What You're Evolving

You are evolving a Python function `generate_candidates(ell, m)` that returns candidate bivariate bicycle (BB) quantum error-correcting code polynomial pairs. Each candidate is a pair of polynomials (A, B) represented as lists of `(x_exponent, y_exponent)` tuples. Polynomials may have 2-6 terms.

Your goal is to discover **new structural families (ansatze)** — algebraic templates relating A and B that produce good codes across multiple lattice sizes. Not individual codes, but repeating patterns.

## Mathematical Background

A BB code is defined over the ring F_2[x,y]/(x^ell - 1, y^m - 1) by two polynomials A(x,y) and B(x,y). Each monomial x^a * y^b corresponds to a shift operator P_m^b (tensor) P_ell^a acting on the ell x m torus.

Code parameters: [[n, k, d]] where n = 2*ell*m, k = logical qubits, d = code distance.

**Figure of merit**: FOM = k * d^2 / n. Higher is better. Target: FOM > 12.0.

## The Scientific Question

**Are there structural families of BB codes beyond the 3 known ones?**

All known good BB codes fall into exactly 3 families:

1. **x/y-swap trinomials**: A = x^a + y^b + y^c, B = y^d + x^e + x^f. One polynomial has one pure-x term and two pure-y terms; the other is the reverse. Best: [[360,12,≤24]] FOM=19.2.

2. **Constant-monomial**: A = 1 + y^a + y^b, B = 1 + x^c + x^d. Both polynomials are univariate with a constant term. Very high k. Best: [[360,40,≤20]] FOM=44.4.

3. **Bravyi et al. standard**: Specific trinomials from arXiv:2308.07915 (these overlap with family 1).

These three families share a property: every term is **pure** — either x^a (with y-exponent 0) or y^b (with x-exponent 0) or the constant 1. No known good code uses a **mixed monomial** x^a·y^b with both a,b > 0. No known good code uses more than 3 terms. These could be fundamental constraints or accidents of limited exploration.

Your goal: discover whether other structural templates exist that produce competitive codes.

## Known Best Codes (the baseline)

| Code | ell | m | A_terms | B_terms | FOM | Family |
|------|-----|---|---------|---------|-----|--------|
| [[72,12,6]] | 6 | 6 | [(3,0),(0,1),(0,2)] | [(0,3),(1,0),(2,0)] | 6.0 | x/y-swap |
| [[144,12,12]] | 12 | 6 | [(3,0),(0,1),(0,2)] | [(0,3),(1,0),(2,0)] | 12.0 | x/y-swap |
| [[288,12,18]] | 12 | 12 | [(3,0),(0,2),(0,7)] | [(0,3),(1,0),(2,0)] | 13.5 | x/y-swap |
| [[360,12,≤24]] | 30 | 6 | [(9,0),(0,1),(0,2)] | [(0,3),(25,0),(26,0)] | 19.2 | x/y-swap |
| [[360,40,≤20]] | 15 | 12 | [(0,0),(0,1),(0,2)] | [(0,0),(5,0),(10,0)] | 44.4 | const-mono |
| [[288,32,≤20]] | 12 | 12 | [(3,0),(0,2),(0,10)] | [(0,6),(1,0),(11,0)] | 44.4 | x/y-swap |

## Directions to Explore

Think about **structural relationships between A and B**, not specific coefficient values. A good ansatz is a template that works at 3+ lattice sizes.

### 1. Mixed monomials (diagonal shifts)

Terms like x^a·y^b with both a,b > 0 create diagonal shifts on the torus, coupling both cyclic dimensions. This entire region is unexplored.

- **Complementary diagonals**: A has shift (a,b), B uses (b,a) or (-b,a) — reflection/rotation on the torus
- **Coordinate transforms**: B = A(x^s, y^t) for coprime s,t — same algebraic structure, different geometry
- **Hybrid**: axis-aligned anchor (like x^3 or 1) + diagonal terms — 4-5 term polynomials mixing pure and mixed terms

### 2. Multi-term polynomials (4-6 terms)

All known good codes use exactly 3 terms. More terms create richer Tanner graph connectivity.

- **4-term extensions of known good trinomials**: Add a carefully chosen 4th term to A or B from a known code
- **Symmetric 4-term**: A and B both have 4 terms with a structural relationship
- **High-connectivity designs**: 5-6 terms creating dense, regular Tanner graphs

### 3. Non-standard pure-term patterns

Pure-x and pure-y terms but in structures that DON'T match x/y-swap or constant-monomial.

- **Mixed-axis with constant**: A = 1 + x^a + y^b (has constant + x-term + y-term), B with a different asymmetric structure
- **Unbalanced pure terms**: A has 2 x-terms + 1 y-term + constant, B has 1 x-term + 2 y-terms (no constant)
- **Non-trivial constant structures**: A = 1 + x^a + x^b (constant + 2 x-terms), B = y^c + y^d + x^e (different mix)

### 4. Algebraic constructions (A-B relationships)

Build B from A using algebraic operations in the quotient ring.

- **Monomial multiplication**: B = x^a · y^b · A — shared ideal structure
- **Ring automorphism**: B = A(x^s, y^t) where (s,t) defines an automorphism of Z_ℓ × Z_m
- **Compositional**: B = A(x^c, 1) or B = A(1, y^c) — evaluate A along one axis
- **Complementary ideals**: A and B chosen so their generated ideals have a specific intersection

### 5. Hybrid patterns (cross-family)

Combine elements from different known families in one code.

- **Constant-monomial A + x/y-swap B**: A = 1 + y^a + y^b, B = y^d + x^e + x^f
- **x/y-swap A + algebraic B**: A = x^a + y^b + y^c, B derived from A by ring automorphism
- **Asymmetric term counts**: A is a trinomial, B has 4-5 terms (or vice versa)

## Known Dead Ends (avoid these)

- **Self-dual (A = B)**: Always d = 2 exactly (proven). Auto-blocked by the evaluator.
- **Univariate without constant term**: A = y^a + y^b + y^c, B = x^d + x^e + x^f (no constant in either). Typically d ≤ 4 (MILP-verified). High k but useless distance.
- **Regenerating exact known codes**: They're already in the safety net — discovering them again wastes evaluation budget.
- **Minor perturbations of known codes**: Small exponent shifts (±1) yield diminishing returns. Focus on structurally different constructions.

## Constraints on Your Function

- Return type: `list[tuple[list[tuple[int,int]], list[tuple[int,int]]]]`
- Each polynomial: 2-6 terms (tuples of (x_exp, y_exp))
- Exponent ranges: 0 <= x_exp < ell, 0 <= y_exp < m
- All terms in each polynomial must be distinct
- Reject self-dual pairs (A = B) — always d = 2
- Target: 100-2000 candidates per lattice. Quality over quantity.
- Use standard Python + numpy only

## Evaluator Feedback

### Metrics

| Metric | Meaning | What to optimize |
|--------|---------|-----------------|
| `combined_score` | Primary fitness: sum of best credible FOM per lattice | Maximize |
| `best_fom` | Highest FOM across all lattices | Target > 12.0 |
| `num_valid` | Candidates with k > 0 | Higher = better algebraic structure |
| `num_above_6` | Codes with FOM >= 6.0 | Breadth of good codes |
| `total_candidates` | Total generated | Keep in 100-2000 range per lattice |

### Artifacts

- **`best_code`**: Top code found with A and B terms, structural breakdown (mixed vs pure term counts, shift directions). Study the relationship between A and B — what structural property made it work?
- **`structural_analysis`**: For codes with d >= 4, reports term classification (pure-x, pure-y, constant, mixed) and shift vectors. Use this to identify repeating patterns.
- **`summary`**: Aggregate stats across all evaluated lattices.
- **`errors`**: Runtime errors. Common: `returned NoneType` (forgot return), `candidates capped` (too many — prune).

### Evaluation Stages

1. **Stage 1** (~2s): k-only on (6,6) and (12,6). Must produce some k > 0 codes to advance. Safety-net codes (outside your control) ensure this — focus on generating novel codes that ALSO have k > 0.
2. **Stage 2** (~30-60s): Full distance estimation on 8 lattices via BP-OSD. Distance filtered by d/sqrt(n) ratio — only codes with d <= 1.3*sqrt(n) are trusted.

### Tips

1. **If most candidates have k = 0**: Try adding a constant term (0,0) — the identity operator often stabilizes the kernel. Or try pure-term structures first to understand k behavior.
2. **If k > 0 but d ≤ 2**: The algebraic structure is too regular. Try breaking symmetry: larger exponents, coprime shift vectors, asymmetric A/B structures.
3. **If a code has d >= 4**: This is the key signal. Study the A-B relationship in the structural_analysis artifact. What connects A and B? Encode that relationship as a generation strategy that works across lattice sizes.
4. **Think in templates, not instances**: A single good code at one lattice is noise. A structural relationship that produces k > 0 at three lattice sizes is an ansatz.
5. **Try diverse structures in parallel**: Don't converge on one approach too early. Keep generating candidates from multiple directions — mixed monomials, multi-term, non-standard pure-term, algebraic constructions, and hybrids.
