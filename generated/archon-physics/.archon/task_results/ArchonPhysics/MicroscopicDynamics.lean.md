# ArchonPhysics/MicroscopicDynamics.lean

## Summary

- Declarations added: **0**. The API-locked source already contains precisely the 17 permitted public declarations, all fully proved.
- Declarations blocked: **0**. There is no unfinished proof obligation in the assigned module, and the closed public surface prohibits adding a new public infrastructure lemma.
- Sorry count: **0 → 0**. The source contains no `sorry`, `admit`, or `axiom`.
- Source change: **none**. The file matches the iteration-007 baseline byte-for-byte.
- Verification: `lake build ArchonPhysics.MicroscopicDynamics` completed; Lean LSP reports no errors (only the pre-existing short-copyright-header warning at line 1).

## Existing API review (lines 19–352)

- **Approach:** Read the blueprint and DAG closure, then searched the current Mathlib API. `lean_leansearch` found `IsPicardLindelof.of_contDiffAt_one` and `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`; `lean_loogle` found `HasDerivAt.add`; direct signature checks confirmed `ODE_solution_unique_of_eventually`, `HasDerivAt.fun_sum`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, and `Lattice.sum_forwardDifference`.
- **Result:** RESOLVED — no construction was required. The existing locked declarations are present with their specified signatures: `PhaseSpace`, `interactionPotential`, `interactionForce`, `latticeForce`, `microscopicVectorField`, `IsClassicalSolutionAt`, `IsGlobalClassicalSolution`, `hamiltonianEnergy`, `totalMomentum`, `latticeForce_apply`, `sum_latticeForce`, `microscopicVectorField_contDiff`, `exists_unique_local_solution_germ`, `totalMomentum_hasDerivAt_zero_at`, `hamiltonianEnergy_hasDerivAt_zero_at`, `hamiltonianEnergy_eq_of_forall_mem_uIcc`, and `totalMomentum_eq_of_forall_mem_uIcc`.
- **Axiom evidence:** Lean LSP independently verified every theorem at lines 65–352 — `latticeForce_apply`, `sum_latticeForce`, `microscopicVectorField_contDiff`, `exists_unique_local_solution_germ`, `totalMomentum_hasDerivAt_zero_at`, `hamiltonianEnergy_hasDerivAt_zero_at`, `hamiltonianEnergy_eq_of_forall_mem_uIcc`, and `totalMomentum_eq_of_forall_mem_uIcc` — with exactly `propext`, `Classical.choice`, and `Quot.sound`; source scanning returned no suspicious patterns.

## Needs blueprint entry

No non-private declaration was added in this session, so there is no new `lean_aux` infrastructure to blueprint. The existing `blueprint/src/chapters/ArchonPhysics_MicroscopicDynamics.tex` already contains one block for each of the 17 API-locked declarations. Its blocks are ready for the normal post-prover `sync_leanok` pass; I did not modify blueprint markers because prover permissions prohibit blueprint edits.

## Why I stopped

- **Real progress:** 0 new axiom-clean declarations. The existing axiom-clean locked surface was independently confirmed rather than altered; the source is unchanged from the iteration baseline.
- **Infrastructure already exists:** `IsPicardLindelof.of_contDiffAt_one`, `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, `ODE_solution_unique_of_eventually`, `HasDerivAt.fun_sum`, and `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` provide the exact ODE and calculus ingredients used by the current proofs.
- **No permitted adjacent step:** a public helper would violate the explicit closed API, while a private helper would not shrink any remaining gap. Thus further Lean edits would not satisfy the assigned objective.
- **Informal agent:** not applicable: there was no unresolved mathematical blocker. The environment also has no configured `DEEPSEEK`, `MOONSHOT`, `OPENROUTER`, `OPENAI`, or `GEMINI` key.
- **Approaches written but not attempted:** none.
