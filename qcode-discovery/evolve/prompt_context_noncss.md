# Non-CSS PBB Code Discovery — Domain Knowledge for LLM

## What You're Evolving

You are evolving a Python function `generate_candidates(ell, m)` that returns candidate **non-CSS perturbed bivariate bicycle (PBB)** quantum error-correcting codes. Each candidate is a 4-tuple `(A_terms, B_terms, C_terms, D_terms)` of polynomial exponent pairs.

## Mathematical Background

A PBB code extends the bivariate bicycle (BB) code by adding perturbation polynomials to the stabilizer matrix:

```
Block 1 (mixed):   x-part = [A | B],   z-part = [C | D]   (C left, D right, paper convention)
Block 2 (pure Z):  x-part = [0 | 0],   z-part = [B^T | A^T]
```

When C = D = 0, this is exactly a CSS BB code. Non-zero C, D make the code **genuinely non-CSS** — it cannot be transformed to CSS by any single-qubit Clifford operations.

Each polynomial is defined over `F_2[x,y]/(x^ℓ-1, y^m-1)`:
- A, B: base polynomials (exactly 3 terms each)
- C, D: perturbation polynomials (1+ terms each)
- Exponents: `0 ≤ x-exp < ℓ`, `0 ≤ y-exp < m`
- Each term is `(x_exponent, y_exponent)`

Code parameters:
- n = 2·ℓ·m physical qubits
- k = logical qubits (depends on A, B, C, D together)
- d = code distance (adaptive: exact d≤6 at n≤216, exact d≤4 at n>216, MILP for rest)

**Commutativity constraint**: `(A @ C^T + B @ D^T) % 2` must be symmetric. The evaluator checks this automatically — invalid candidates are silently dropped, but generating many invalid candidates wastes your budget.

## Scoring

FOM = k·d²/n — higher is better.

**Codes with d ≤ 4 score ZERO.** The evaluator has a 3-tier adaptive distance pipeline:

1. **Hash-based exact check** (O(n³) symplectic weight):
   - n ≤ 216: checks d ≤ 6 (exact). ~5s at n=72, ~80s at n=180, ~2min at n=216.
   - n > 216: checks d ≤ 4 only (<1s). The O(n³) triple loop is too slow for weight-5/6 at n=360.
2. **MILP symplectic** for codes beyond hash range: Adaptive timeouts (15-60s per logical). Partial results are valid upper bounds even if not all 2k logicals solve in time.
3. **BP-OSD fallback**: Only used if MILP yields nothing. Known to overestimate for non-CSS codes.

**Key implications**:
- At (6,6) n=72: d≤6 is exact. Any FOM > 6.0 at this lattice is verified.
- At (12,6) n=144 or (15,6) n=180: d≤6 is still exact.
- At (30,6) n=360: d≤4 is exact (rejects bad codes fast), d≥5 uses MILP (slower but gives valid bounds).

## State of the Art — What We've Found

### Best PBB codes at (6,6), n=72 (MILP-verified distances):

| Code | k | d | FOM | C terms | D terms | Notes |
|------|---|---|-----|---------|---------|-------|
| **[[72,12,6]]** B2a | 12 | 6 | **6.0** | 2 terms | 3 terms | Campaign 7c best |
| **[[72,12,6]]** B2b | 12 | 6 | **6.0** | 2 terms | 2 terms | |
| **[[72,12,6]]** B7e | 12 | 6 | **6.0** | 3 terms | 2 terms | Campaign 7e, new base |
| [[72,10,6]] known | 10 | 6 | 5.0 | 2 terms | 4 terms | Pre-campaign baseline |

### CSS comparison (same block length):
- CSS Gross [[72,12,6]]: FOM = 6.0 — PBB matches but doesn't exceed this yet
- CSS Gross [[144,12,12]]: FOM = 12.0

**Target**: Beat FOM=6.0 at any lattice. Larger lattices have more room:
- d=8 at n=144 with k=12 → FOM=5.3
- d=10 at n=180 with k=12 → FOM=6.7 (beats current best!)
- d=14 at n=360 with k=20 → FOM=10.9

### Key observations:

1. **Two known (6,6) bases with d≥5**:
   - Base 2: A=[(1,2),(4,3),(4,4)], B=[(0,0),(1,5),(5,4)] → k=10-12, d=6
   - Base 7e: A=[(2,1),(3,1),(4,4)], B=[(0,0),(5,1),(4,5)] → k=12, d=6

   **Campaign 7d found ~230 new bases with d≥3, but ALL had d≤4 on verification.**
   **Finding a new base with d≥5 is the critical challenge.**

2. **Commutativity is extremely restrictive** (~0.04% hit rate with random C,D). Don't waste budget on random C,D — use structured perturbations around known good codes.

3. **d≤4 is the dominant failure mode**:
   - Many A,B bases have weight-2/3/4 logicals structurally
   - The d≤6 check is EXACT (hash-based, ~5s for n=72)
   - Distances d=5 and d=6 are verified — the evaluator is trustworthy now
   - Discovering NEW bases with d≥5 is the key to progress

4. **C,D term count**: Best codes use 2-3 terms each. The sweet spot is compact perturbations.

5. **(9,6) n=108 lattice**: Now evaluated! Could yield higher FOM at larger n. Try extending Base2/Base7e exponents to (9,6).

## What Does NOT Work

### 1. Most A,B bases → d≤4
- Base1 A=[(0,3),(0,4),(3,2)], B=[(0,2),(2,2),(4,2)]: ALWAYS d=2 with any C,D
- Base6 A=[(0,1),(2,3),(4,5)], B=[(1,0),(3,2),(5,4)]: CSS d=2, PBB d=2
- Campaign 7d "new bases" (e.g. A=[(1,0),(2,1),(3,2)]): k=16 but d=4 (BP-OSD falsely reported d=10)
- Arithmetic-progression bases (e.g., exponents 0,2,4): often have column degeneracy → d=2
- **TEST**: Before investing in C,D optimization, verify your A,B base doesn't give d=2

### 2. Self-dual perturbation (C = D)
- ALWAYS gives d=2. Never generate C equal to D.

### 3. CSS (C=D=empty) — No perturbation
- Just gives a BB code. Misses the non-CSS advantage entirely.

### 4. Perturbations that don't satisfy commutativity
- (A @ C^T + B @ D^T) % 2 must be symmetric
- For Base2, only ~0.04% of random C,D pass — use structured generation

## Strategies to Explore

### HIGHEST PRIORITY: Discover new A,B bases with d≥5

This is the most impactful direction. Only Base2 and Base7e achieve d≥5 at (6,6). Finding another would open up entirely new code families. Try:
- Mixed monomial patterns (terms with both x,y > 0)
- Translations of Base2/Base7e: shift all exponents by constants
- Permutations/reflections of Base2 exponent structure
- Bases where the CSS code already has d≥3 (check before adding perturbation!)
- The d≤6 check is now EXACT — any d≥5 code you find is real, not a BP-OSD artifact

### HIGH PRIORITY: Optimize C,D for Base2/Base7e

Since commutativity is rare, use structured approaches:
- Perturb known good C,D by ±1 on each coordinate
- Add/remove one term at a time from known good perturbations
- Focus on 2-3 term C and 2-3 term D (the sweet spot)
- Try all 2-term C × 2-term D combinations that satisfy commutativity (feasible with pre-check)

### HIGH PRIORITY: Explore larger lattices

Larger lattices have more room for higher distance codes:

| Lattice | n | FOM example | Distance method |
|---------|---|-------------|-----------------|
| (9,6) | 108 | d=8, k=12 → FOM=7.1 | d≤6 exact, MILP d≥7 |
| (12,6) | 144 | d=8, k=12 → FOM=5.3 | d≤6 exact, MILP d≥7 |
| (15,6) | 180 | d=10, k=12 → FOM=6.7 | d≤6 exact, MILP d≥7 |
| (30,6) | 360 | d=14, k=20 → FOM=10.9 | d≤4 exact, MILP d≥5 |

**Strategies for larger ℓ**:
- Known bases (Base2, Base7e) have x-exponents < 6 — they work at any ℓ≥6
- Shift x-exponents by ℓ/2 or ℓ/3 to explore wider space
- Generate new bases with exponents spanning [0, ℓ)
- At n=360, MILP gives partial results (min over solved logicals = valid upper bound)

### MEDIUM PRIORITY: (6,3) and (3,6) lattices

Base3/Base4 at (6,3) give k=4 codes with d≥3. Smaller but valid. Try:
- New perturbations for Base3/Base4
- New bases at (6,3)

## Constraints on Your Function

- Must return `list[tuple[list[tuple[int,int]], list[tuple[int,int]], list[tuple[int,int]], list[tuple[int,int]]]]`
- A_terms, B_terms: exactly 3 distinct tuples each (trinomials)
- C_terms, D_terms: at least 1 tuple each (non-empty for non-CSS)
- x-exponents in [0, ell), y-exponents in [0, m)
- All terms within each polynomial must be distinct
- Keep total candidates < 3000 per lattice
- Use standard Python + numpy only
- **NEVER make C_terms equal to D_terms** (self-dual trap → d=2)
- **NEVER return empty C or D** (that's CSS, not non-CSS)
- **Pre-check commutativity** before adding candidates — saves budget

## Evaluator Feedback

### Metrics
| Metric | Meaning |
|--------|---------|
| `combined_score` | Sum of best FOM per lattice (distances are now reliable) |
| `best_fom` | Highest FOM found |
| `num_valid` | Candidates with k > 0 (passed commutativity + d≥5) |
| `num_high_k` | Codes with k ≥ 8 |

### Evaluation Stages

1. **Stage 1** (quick, ~5s): k-only on (6,6). Must produce valid codes (k > 0).
2. **Stage 2** (full, ~120-1200s): Adaptive distance on 7 lattices ((6,6), (9,6), (12,6), (15,6), (30,6), (6,3), (3,6)). Hash-based exact d≤6 at n≤216, MILP with adaptive timeouts, BP-OSD fallback.

### Tips
1. **If most candidates have d≤4**: Your A,B base likely has structural low-weight logicals. Only Base2 and Base7e produce d≥5 at (6,6).
2. **If num_valid is very low**: Most candidates fail commutativity. Use pre-check and structured generation.
3. **If k is high but d≤4**: The base is bad for non-CSS despite high k. Campaign 7d found k=16 bases that all had d=4. Switch to Base2/Base7e or find a genuinely new base.
4. **Focus on (6,6), (9,6), and larger lattices**: Higher FOM is easier at larger n if d grows proportionally.
5. **Target**: Beat FOM=6.0 at any lattice. d=10 at n=180 with k=12 → FOM=6.7.
6. **Distances are reliable**: d≤6 exact at n≤216, MILP for rest. At n=360, d≤4 is exact and MILP handles d≥5.
7. **At n=360**: MILP gives partial results (valid upper bounds from solved logicals). BP-OSD fills gaps.
