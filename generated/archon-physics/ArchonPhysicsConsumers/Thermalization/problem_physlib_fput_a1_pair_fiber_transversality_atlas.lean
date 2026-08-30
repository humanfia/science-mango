import ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas

/-!
# Consumer: actual A1 pair-fiber transversality audit

This consumer checks the two conclusions that must be kept together:

* the all-signed-term uniform transversality premise is false, witnessed by
  an identically resonant acoustic-copy term whose cubic coefficient is also
  identically zero;
* every regular noncritical actual mismatch has a local injective one-mass
  patch, while the measurable complement is retained explicitly and a
  fixed-order history pays its finite denominator count.

This is deterministic frozen-mass spectral analysis.  It uses no initial
phase law, re-Haar, Markov approximation, pairwise decoherence premise, or
kinetic-limit closure.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.RandomEnsemble
open Set MeasureTheory

noncomputable section

/-- The obstruction is an exact zero-mismatch/zero-coefficient block, not a
small-ball event. -/
theorem consumer_physlibA1_acoustic_obstruction_is_structurally_null
    {N : Nat} [NeZero N] (coupling : Complex)
    (m fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (pair : Real × Real) :
    physlibA1PairMismatchChart fixed site₁ site₂ observed
        (physlibA1AcousticCopyTerm observed) pair = 0 ∧
      freeQuadraticDuhamelCoefficient coupling m observed radius
        (physlibA1AcousticCopyTerm observed) = 0 := by
  exact ⟨physlibA1AcousticCopyTerm_pairMismatch_eq_zero
      fixed site₁ site₂ observed pair,
    physlibA1AcousticCopyTerm_coefficient_eq_zero
      coupling m observed radius⟩

/-- Consumer form of the genuine one-site Jacobian formula. -/
theorem consumer_physlibA1_verticalJacobian_eq_signedModeSum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    {pair : Real × Real}
    (hregular : pair ∈ physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term) :
    physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term pair =
      ∑ r : Fin 3,
        (FreeFPUTCollisionMismatchBridge.quadraticCollisionSign term r).coefficient *
          actualTwoMassModeVerticalJacobian fixed site₁ site₂
            (FreeFPUTCollisionMismatchBridge.quadraticCollisionModes
              observed term r) pair := by
  exact physlibA1PairMismatchVerticalJacobian_eq_signedSum
    fixed hsite observed term hregular

/-- Consumer form of the fixed-order, finite-denominator bad-event loss. -/
theorem consumer_physlibFixedHistory_badEvent_le_card_mul
    {J : Type*} [Fintype J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : J → QuadraticPhaseTerm N) (first : Real)
    (level : J → Nat) (budget : ENNReal)
    (hbudget : ∀ j, massCoordinateLaw
      (physlibA1PairFiberBadLevel fixed site₁ site₂ observed
        (term j) first (level j)) ≤ budget) :
    massCoordinateLaw (physlibFixedHistoryPairFiberBadEvent
        fixed site₁ site₂ observed term first level) ≤
      (Fintype.card J : ENNReal) * budget := by
  exact measure_physlibFixedHistoryPairFiberBadEvent_le_card_mul
    fixed site₁ site₂ observed term first level budget hbudget

#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.physlibA1AcousticCopyTerm_mismatch_eq_zero
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.physlibA1AcousticCopyTerm_coefficient_eq_zero
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.not_injOn_physlibA1AcousticCopyTerm_pairFiber_massSupport
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.no_uniform_positive_A1_pairFiberJacobianLowerBound
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.physlibA1PairMismatchVerticalJacobian_eq_signedSum
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.exists_physlibA1PairFiber_localInjectivePatch
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.mem_physlibA1PairFiberBadLevel_iff
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.measure_physlibFixedHistoryPairFiberBadEvent_le_card_mul
#print axioms consumer_physlibA1_acoustic_obstruction_is_structurally_null
#print axioms consumer_physlibA1_verticalJacobian_eq_signedModeSum
#print axioms consumer_physlibFixedHistory_badEvent_le_card_mul

end

end ArchonPhysicsConsumers.Thermalization
