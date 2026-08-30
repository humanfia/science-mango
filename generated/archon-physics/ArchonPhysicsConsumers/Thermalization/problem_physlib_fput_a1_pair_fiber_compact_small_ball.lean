import ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall

/-!
# Consumer: actual A1 compact pair-fiber small-ball atlas

This consumer keeps the quantitative hypothesis boundary visible.  The actual
one-mass mismatch is restricted to a supplied compact set `K` contained in the
spectrally differentiable locus, and its actual vertical Jacobian is bounded
below there by a supplied `j₀ > 0`.  Compactness turns the local inverse-function
patches into a finite atlas.  The full-law estimate retains the exceptional
mass `massCoordinateLaw Kᶜ`.

For a fixed finite collection of ordinary cumulative denominators, the regular
cost is the explicit sum of the individual atlas constants and the compact
bad event is charged only once.  Indices outside `ordinary` remain in the
separate retained sector; this includes genuine resonant, charge-balanced, or
recollision histories unless separately removed.  The identically resonant
acoustic-copy A1 term is not sent to a small-ball estimate: its interaction
coefficient is exactly zero and is deleted structurally.

No independence between denominator events, initial-phase law, re-Haar step,
Markov approximation, high-order RPA, or kinetic-limit closure is used here.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
open ArchonPhysics.RandomEnsemble
open Set MeasureTheory

noncomputable section

/-- Consumer form of the actual compact-atlas endpoint.  In particular, this
does not claim a uniform Jacobian bound on the whole iid mass support. -/
theorem problem_physlibA1_pairFiberCompact_smallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)|) :
    ∃ atlasCard : Nat,
      (∀ {target : Set Real}, MeasurableSet target →
        Measure.map
            (fun second => physlibA1PairMismatchChart
              fixed site₁ site₂ observed term (first, second))
            (massCoordinateLaw.restrict K) target ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              (volume : Measure Real) target) ∧
      (∀ delta : Real,
        Measure.map
            (fun second => physlibA1PairMismatchChart
              fixed site₁ site₂ observed term (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              ENNReal.ofReal (2 * delta) + massCoordinateLaw Kᶜ) := by
  exact exists_atlasCard_physlibA1PairFiberCompact_smallBall
    fixed hsite observed term first K hK hKregular hj₀ hjac

/-- The zero acoustic-copy block is deleted by its zero interaction
coefficient, rather than being counted among ordinary small-ball events. -/
theorem problem_physlibA1_acousticCopy_structuralDeletion
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

/-- The supplied ordinary sector and the retained resonant/recollision sector
form a disjoint partition of every fixed-order finite index type. -/
theorem problem_physlibFixedOrder_ordinary_retained_partition
    {J : Type*} [Fintype J] [DecidableEq J] (ordinary : Finset J) :
    ordinary ∪ physlibFixedOrderRetainedSector ordinary = Finset.univ ∧
      Disjoint ordinary (physlibFixedOrderRetainedSector ordinary) := by
  exact ⟨ordinary_union_physlibFixedOrderRetainedSector_eq_univ ordinary,
    ordinary_disjoint_physlibFixedOrderRetainedSector ordinary⟩

#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall.scalarFinitePatchAtlas_smallBall_le
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall.exists_atlasCard_physlibA1PairFiberCompact_smallBall
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall.ordinary_union_physlibFixedOrderRetainedSector_eq_univ
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall.ordinary_disjoint_physlibFixedOrderRetainedSector
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall.exists_atlasCard_physlibFixedOrderOrdinaryNearEvent_le
#print axioms
  ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas.physlibA1AcousticCopyTerm_coefficient_eq_zero
#print axioms problem_physlibA1_pairFiberCompact_smallBall
#print axioms problem_physlibA1_acousticCopy_structuralDeletion
#print axioms problem_physlibFixedOrder_ordinary_retained_partition

end

end ArchonPhysicsConsumers.Thermalization
