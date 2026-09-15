# Finite polynomial factor certificate replay — preparation only

No model worker is started before CompactStorage exits. This plan has not been frozen or accepted.

Use binary polynomials throughout. Enumerate the finite pool of coefficient functions Fin(n+1)→ZMod2 and reconstruct ∑i C(coeff i)*X^i. This is an actual finite enumeration, with a completeness lemma for every polynomial of natDegree≤n. For a candidate p, check monicity and p≠1, then search the finite pool at n=p.natDegree/2 for a monic divisor q satisfying 0<q.natDegree≤n. Each divisibility check is the actual polynomial remainder/equality test. Reject when such q exists. No Classical.decide Irreducible is used as the implementation.

The local primary interface is Mathlib/Algebra/Polynomial/Monic.lean, Monic.irreducible_iff_lt_natDegree_lt (lines352–354), which identifies irreducibility with absence of exactly those bounded monic divisors. This applies over ZMod2 and includes repeated factors in a larger product; no squarefree hypothesis is introduced.

The factor certificate is a finite list of polynomial/positive-exponent pairs. Its checker checks each polynomial with the finite irreducibility test, positive exponents (and distinct factor entries if the chosen canonical record requires them), and the literal product ∏p^e equals the recorded full signature. The empty list certifies signature1. The product check retains every multiplicity.

Bounded target plan (about three targets):

1. **pool_complete**: reconstructed finite coefficient pool contains every degree-bounded binary polynomial, and its members satisfy that bound.
2. **irreducible_check_exact**: the actual bounded-divisor Boolean test succeeds iff the candidate is monic and irreducible.
3. **factor_check_exact**: actual list checker succeeds iff positive exponents, checked monic irreducible factors, and the literal factor-power product equality all hold. A valid supplied factor list passes the same checker. This proves verification; it does not demand a new factor-discovery algorithm beyond the original scope.

Connect the recorded product polynomial to the actual recipe signature through label_replay.check_sound. Auxiliary factor/pin replay artifacts do not silently become part of the compact core storage bound, which explicitly excludes optional transcripts. No hash-only acceptance, supplied irreducibility predicate, serialization parser, Lean codegen or timing claim is added.
