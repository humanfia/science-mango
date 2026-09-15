# Proposed CRT connectivity repair route (not a proof receipt)

Source: reviewed M5 PROOF.md, section 5. This note is library research only: no targets below have yet been compiled or proved. No active formalization project was edited and no model was launched. The original proof permits any residue avoiding one forbidden class; the concrete choice below is a convenient instantiation, not an additional hypothesis.

The exact required end target is:

```lean
∀ δ T e w : ℕ,
  0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 →
  ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1
```

There is no requirement that e or w be positive. The bound is the original strict k < w + δ (equivalent to its integer k ≤ w + δ - 1). Neither a smaller bound nor an efficient implementation is needed.

Use these candidate definitions in a future foundation module:

```lean
def repairResidue (e p : ℕ) : ℕ := if p ∣ e then 1 else 0
def primeProduct (δ : ℕ) : ℕ := ∏ p ∈ δ.primeFactors, p
```

The product needs `open scoped BigOperators`. Suggested imports:
`Mathlib.Data.Nat.ChineseRemainder`,
`Mathlib.Data.Nat.Factorization.Basic`,
`Mathlib.Data.Nat.Prime.Basic`, and a suitable arithmetic tactic import.

## Five candidate nodes

1. Local safe residue, no CRT dependency:

```lean
∀ p δ T e : ℕ,
  p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 →
  ¬ p ∣ e + repairResidue e p * T
```

Split on p | e. In the false case the residue is zero, immediately giving the conclusion. In the true case the residue is one. If p also divided T, `Nat.dvd_gcd` twice would make p divide 1, contradicting primality. Thus p does not divide T; since p divides e it cannot divide e+T. This works for p=2 without a special residue-count argument.

2. CRT residue realization, independent of node 1:

```lean
∀ δ e : ℕ, 0 < δ →
  ∃ r : ℕ, r < primeProduct δ ∧
    ∀ p ∈ δ.primeFactors, Nat.ModEq p r (repairResidue e p)
```

Apply `Nat.chineseRemainderOfFinset` with indices `δ.primeFactors`, modulus function `fun p => p`, and residues `repairResidue e`. Its returned subtype stores the congruences. `Nat.chineseRemainderOfFinset_lt_prod` supplies the bound. Distinct prime factors are coprime by `Nat.coprime_primes`; each modulus is nonzero by `Nat.prime_of_mem_primeFactors` and `Nat.Prime.ne_zero`.

3. Place a residue in the required interval, independent of prime theory:

```lean
∀ R r w : ℕ, 0 < R →
  ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r
```

A natural-number witness avoiding subtraction side conditions on r and w is
`k = w + (r + (R - 1) * w) % R`.
The interval is immediate from `Nat.mod_lt`. For congruence, use
`(R - 1) * w + w = R * w`, valid since R>0, and `Nat.add_mod` to compute k modulo R. This auxiliary modular representative lemma is sufficient; it does not require choosing a least element or an integer-to-natural conversion.

4. All chosen prime residues imply repaired connectivity, depending on node 1:

```lean
∀ δ T e k : ℕ,
  0 < δ → Nat.gcd (Nat.gcd T δ) e = 1 →
  (∀ p ∈ δ.primeFactors, Nat.ModEq p k (repairResidue e p)) →
  Nat.gcd δ (e + k * T) = 1
```

Use `Nat.coprime_of_dvd` (whose result unfolds to gcd=1). For each prime divisor p of δ, `Nat.Prime.mem_primeFactors` gives membership. Transport the congruence through multiplication by T and addition of e via `Nat.ModEq.mul_right` and `Nat.ModEq.add_left`. Then `Nat.ModEq.dvd_iff` with `dvd_refl p` transfers divisibility to the expression excluded by node 1.

5. Assemble bounded repair, depending on nodes 2, 3 and 4:

```lean
∀ δ T e w : ℕ,
  0 < δ → 0 < T → Nat.gcd (Nat.gcd T δ) e = 1 →
  ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1
```

Set R=primeProduct δ. R>0 because every prime factor is positive (`Finset.prod_pos`). Also `Nat.prod_primeFactors_dvd δ` gives R|δ, hence `Nat.le_of_dvd` and δ>0 give R≤δ. Use node 2 for r, node 3 for k. For each p in δ.primeFactors, `Finset.dvd_prod_of_mem` gives p|R; `Nat.ModEq.of_dvd` descends k≡r mod R to mod p, then transitivity combines the CRT congruence. Node 4 proves gcd=1; k<w+R≤w+δ is the exact final bound.

## Pinned Mathlib source observations

Checked directly in the currently pinned source:

- `Data/Nat/ChineseRemainder.lean`: `chineseRemainderOfFinset` returns `{k // ∀ i ∈ t, k ≡ a i [MOD s i]}` and requires nonzero moduli and `Set.Pairwise t (Coprime on s)`; `chineseRemainderOfFinset_lt_prod` supplies the strict product bound.
- `Data/Nat/Factorization/Basic.lean`: `Nat.prod_primeFactors_dvd` has no positive-input assumption; use δ>0 only for the ensuing numerical bound.
- `Data/Nat/PrimeFin.lean`: `Nat.mem_primeFactors`, `Nat.Prime.mem_primeFactors`, `Nat.prime_of_mem_primeFactors`, `Nat.dvd_of_mem_primeFactors`, `Nat.pos_of_mem_primeFactors`.
- `Data/Nat/Prime/Defs.lean`: `Nat.coprime_of_dvd` turns exclusion of every common prime divisor into coprimality.
- `Data/Nat/Prime/Basic.lean`: `Nat.coprime_primes` identifies coprimality of primes with inequality.
- `Data/Nat/ModEq.lean`: `Nat.ModEq.of_dvd`, `.mul_right`, `.add_left`, `.dvd_iff` supply transport without root arguments or extra assumptions.

For δ=1 the factor set is empty, R=1, CRT gives r=0, and the interval contains exactly k=w; gcd 1 _=1. This is covered by the same construction. For p=2, the explicit 0/1 residue is always safe by the same gcd argument. Prime powers in δ need no separate CRT constraints: excluding divisibility by their base prime already ensures gcd=1.

The ready parallel wave is nodes 1, 2 and 3; node 4 waits only for node 1, and node 5 waits for nodes 2, 3 and 4. This is the missing connectivity-repair existence argument itself, not a stronger gate on packing or on M5.
