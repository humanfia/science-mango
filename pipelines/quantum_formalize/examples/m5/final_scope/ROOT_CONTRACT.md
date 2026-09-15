# Exact final contract proposal

This is a clause specification for a final Lean conjunction/record; it does not freeze new declarations. Use the existing arithmetic definitions and actual recovery definitions when they are ready. Names `recoverOrder` and `recoverResidues` below are descriptive placeholders for those concrete definitions, not new parameters or assumed oracles.

Fix `w : ℕ`, `F : BinaryPolynomial`, with `0<w`, `F.Monic`, `F.coeff 0=1`. Let

- `T = signaturePeriod F = PeriodSearch.finiteSearch F`;
- `L = packingCutoff w T = w*T*(T+2)`;
- `B = birthBound w T = L + 2^(w*T)`;
- `A = ResidueCount.A w F`, `C N = OrderCount.C N w F`;
- `R N S U = PhysicalOrder.realizes N w F S U` and `ExistsAt N = ∃ S U, R N S U`.

The public root has only the original parameter hypotheses above. In particular, no physical witness, feasible pattern, correct-count oracle, missing source, nonzero residue polynomial, squarefree signature, or unproved imported lemma may occur as an extra hypothesis.

## All positive weights

1. **Period correctness and finite search.** `0<T`, and for every N, `F∣M_N ↔ T∣N`; the explicit finite search returns T. Include the already accepted F=1 convention. This is independent of realizability.
2. **Fixed-order arithmetic semantics.** For every N>0, `0≤C N`, `0<C N ↔ ExistsAt N`, and `C N=0 ↔ ¬ExistsAt N`. Retain the exact-cardinality identity for the anchored ordered-pair count on its admitted divisor domain, plus the actual zero guards outside that domain. This expresses exact counts, not merely a sufficient positivity test.
3. **Physical recovery from positive C.** For every N>0 with `0<C N`, the concrete arithmetic-prefix recovery terminates after at most `2*(N−1)` binary position decisions and its decoded supports satisfy `R N`. Its count argument is the actual conditional divisor/character formula, not a free function satisfying assumed axioms.
4. **Necessary lower orders.** `R N S U` implies `T∣N` and `max(w,F.natDegree+1)≤N`.
5. **Weight-one branch.** If w=1, `R N S U ↔ N=1 ∧ F=1 ∧ S={0} ∧ U={0}`. This handles the positive-weight boundary without extending the w≥2 global-A theorem beyond its original statement.

## The w≥2 branch

6. **Global arithmetic criterion.** `0≤A`, `(0<A ↔ ∃ N, ExistsAt N)`, and `(A=0 ↔ ¬∃ N, ExistsAt N)`.
7. **Residue recovery.** If `0<A`, the concrete conditional-R recovery returns feasible anchored period tuples, permitting repeated residues and zero tuple polynomials. Its output length is `2*(w−1)` tail coordinates and it makes at most `2*(w−1)*T` candidate tests. The tuple count used for branch choices is the original arithmetic conditional formula.
8. **Actual bounded source and same-support progression.** If `0<A`, obtain S,U,N₀,E with `0<E`, `N₀<B`, and `∀j, R (N₀+j*E) S U`. Keep the exact accepted inequality; it implies the source's “at most B.” The finite constructor uses recovered residues and the established packing/CRT/period steps. This does not assert that the fixed-support progression exhausts all later admissible orders.
9. **Actual bounded first birth.** For
   `K={N≤B : max(w,F.natDegree+1)≤N ∧ T∣N ∧ 0<C N}`,
   the actual `ArithmeticWorkflow.birth w F` is its finite minimum, or `none` when K is empty. Under `0<A`, it returns `some b`, with `b∈K`, `ExistsAt b`, and `∀N, ExistsAt N → b≤N`. Moreover `birth w F=none ↔ A=0`. The construction theorem discharges nonemptiness; it is not an extra root premise. Apply physical recovery at b to obtain the birth recipe.
10. **Every later proposed order.** If `birth w F=some b` and `b≤N`, then
    `(¬T∣N ∨ C N=0) ↔ ¬ExistsAt N`.
    Whenever `0<C N`, the same concrete physical recovery from clause3 returns a valid exact-signature recipe. There is no bound restriction on later proposed N and no change of count formula after birth.
11. **Finite arithmetic workflow.** All evaluations and decisions in the previous clauses are the actual finite factor/divisor/character/power/binomial computations and finite searches/recursions described in TERMINATION.md. Semantic cardinalities establish correctness; they are not substituted as the evaluator or as a raw pair-search procedure.

Normalization41 certifies the correspondence from unanchored recipe inputs to this anchored convention. It belongs in the definition-correspondence evidence, or may be included as an additional proved field; it must not be replaced by the false assertion that unanchored raw exponent gcd is translation invariant.

## Packaging

A single final theorem of the schematic shape

`∀ w F, 0<w → F.Monic → F.coeff 0=1 → OriginalM5Spec w F`

is suitable, provided `OriginalM5Spec` expands to the clauses above with fixed existing arithmetic and recovery definitions. An explicit conjunction with separate w=1/w≥2 cases is equally suitable. The record form is packaging, not a new research target.

The exact-cardinality, lower-bound and finite-search membership lemmas may be referenced through a verified bundled record rather than reproved. Likewise, a root import check can use separately named actual algorithm-correctness fields. What matters is that the one public result contains the complete original contract and its dependency closure is accepted; an arbitrary new monolithic proof style is not required.
