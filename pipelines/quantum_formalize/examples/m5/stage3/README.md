# M5 stage 3: finite quotient period foundation

Draft targets for the next experiment, not accepted proofs. These six targets translate the actual quotient-ring argument of reviewed PROOF.md sections 1, 4 and 5. The quotient is AdjoinRoot F over ZMod 2, including F = 1 and repeated factors. No irreducibility, squarefreeness or nontriviality assumption is introduced.

The first three nodes can run in parallel: finite quotient, explicit inverse for X, and the divisibility/power bridge. The period law waits for all three. The F = 1 boundary check and period divisibility under F | G then run in parallel. The last theorem supplies T | E in section 5. Maximum useful concurrency for this stage is three; the global cap can remain 16.

M5Period.lean imports only the previously accepted foundation plus Mathlib. It does not depend on stage 2, so the statements remain stable if a stage-2 proof requires repair. The source and graph are staged here only; install the definitions into the target project after its active experiment has finished. Run the controller's statement preflight before freezing an experiment receipt. Statement preflight runs in the isolated project /home/jing/m5-lean-period-formalization; no model run is launched while preparing this draft. Its result is recorded separately.

Known library route in the pinned Mathlib: Polynomial.Monic.finite_adjoinRoot and Module.finite_of_finite; Polynomial.X_mul_divX_add and AdjoinRoot.mk_self; AdjoinRoot.mk_eq_zero and mk_X; IsUnit.isOfFinOrder; IsOfFinOrder.orderOf_pos; orderOf_dvd_iff_pow_eq_one. These are concrete polynomial-to-quotient bridge obligations, not an assumption that a suitable finite group or period already exists.

This stage does not prove the numerical bound t(F) ≤ 2^natDegree(F). The next extension must establish quotient cardinality from AdjoinRoot.basis and bound the cyclic subgroup by the finite ring cardinality. The stricter nonconstant bound 2^degree - 1 is unnecessary for the original bound and should not become an added gate. Counting identities, CRT connectivity repair and the full M5 root theorem remain outstanding.

The period definition currently uses noncomputable orderOf. The period_law proves mathematical existence and exact order divisibility, not yet an executable implementation of the finite multiplication algorithm described in the source. Algorithm/refinement work remains explicit and is not marked complete by these six targets.

For the cardinality extension, the actual monic basis name in this pinned version is AdjoinRoot.powerBasisAux' hF. Its equivFun identifies the quotient with Fin F.natDegree → ZMod 2, giving Nat.card = 2^F.natDegree even at degree zero. The general monoid lemma orderOf_le_card then directly bounds the period by the ring cardinality, avoiding any unnecessary nonconstant or strict-bound assumption.
