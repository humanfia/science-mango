import Submission.Kakeya.ConvexFactoring.PostAssemblyHeavySelection
import Submission.Kakeya.ConvexFactoring.TubeParentInducedDensity

/-!
# Post-assembly tube density composition

This module specializes the genuine post-assembly re-heavy construction to a
coarse tube partition.  Fiber nonemptiness and the common fiber-cardinality
bound are discharged by the partition certificates.  The final density bound
is then derived from the actual post-heavy dense witness via
`lambda_div_loss_le_selected_neighborhoodDensity`; it is not an input.

The selected-parent neighborhood density, all multiplicity bounds, and the
mass-retained shading below use the same final refinement.  The displayed
density denominator is `768 * (2 * amplifiedLoss)`, i.e. `1536 *
amplifiedLoss`; `amplifiedLoss` itself contains the actual assembly loss.
The fiber, branching, containment, and scale certificates come from the
supplied `CoarseTubePartition P`.  Recomputed multiplicities remain one-sided
bounds.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open HeavyParentSelection
open NeighborhoodTubeMultiplicityAssembly
open PostAssemblyHeavySelection
open TubeParentInducedDensity

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace PostAssemblyTubeDensity

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}

/-- Actual neighborhood multiplicity assembly, rerun heavy selection on its
final shading, and the tube parent-density lemma produce one common final
shading carrying all conclusions. -/
theorem exists_postAssembly_heavyParentLabel_bucket_with_selectedTubeDensity
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily)
    (lambda L : ℝ≥0∞) (label : κ → β)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal :
      lambda * activeBodyMass P.asConvexFactorization ≤
        L * activeShadingMass P.asConvexFactorization Y)
    (hmass0 : activeShadingMass P.asConvexFactorization Y ≠ 0)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    ∃ A : Assembly P.asConvexFactorization Y
        P.asConvexFactorization.index.coarse (rho : ℝ)
        (P.branchingLoss * P.branching),
      ∃ b : β,
        let parents :=
          postHeavyParents P.asConvexFactorization A lambda L label b
        let R :=
          postHeavyRefinement P.asConvexFactorization A lambda L label b
        parents ⊆ P.asConvexFactorization.index.coarse ∧
          WithinFactor
            (assemblyLoss P.asConvexFactorization
                (P.branchingLoss * P.branching) *
              (2 * Fintype.card β))
            (activeShadingMass P.asConvexFactorization Y)
            R.shading.shadingMass ∧
          parents.Nonempty ∧
          HasDenseFiberWitness P.asConvexFactorization R.shading
            parents lambda
              (2 * amplifiedLoss P.asConvexFactorization
                (P.branchingLoss * P.branching) L) ∧
          (∀ x, R.shading.pointMultiplicity x ≤
            A.outerLevel * A.fiberLevel) ∧
          (∀ x,
            P.asConvexFactorization.neighborhoodOuterMultiplicity
                R.shading (rho : ℝ) x ≤
              frozenNeighborhoodOuterStatistic
                P.asConvexFactorization
                P.asConvexFactorization.index.coarse
                A.fiberRefinement.shading (rho : ℝ) x) ∧
          (∀ x ∈ R.shading.shadedUnion,
            frozenNeighborhoodOuterStatistic
                P.asConvexFactorization
                P.asConvexFactorization.index.coarse
                A.fiberRefinement.shading (rho : ℝ) x =
              A.outerLevel) ∧
          (∀ k ∈ P.asConvexFactorization.index.coarse, ∀ x,
            P.asConvexFactorization.fiberMultiplicity
              R.shading k x ≤ A.fiberLevel) ∧
          (∀ i x, x ∈ R.shading.carrier i →
            P.asConvexFactorization.fiberMultiplicity
              Y (P.asConvexFactorization.index.parent i) x =
                A.fiberLevel) ∧
          lambda /
              (768 *
                (2 * amplifiedLoss P.asConvexFactorization
                  (P.branchingLoss * P.branching) L)) ≤
            (selectedCoarseShading
              (P.asConvexFactorization.neighborhoodInducedShading
                R.shading (rho : ℝ)) parents).shadingDensity := by
  have hrReal : 0 < (rho : ℝ) := by
    exact_mod_cast hrhoPos
  have hfiber :
      ∀ k ∈ P.asConvexFactorization.index.coarse,
        (P.asConvexFactorization.index.fiber k).Nonempty := by
    intro k hk
    exact P.fiber_nonempty hk
  have hM :
      ∀ k ∈ P.asConvexFactorization.index.coarse,
        (P.asConvexFactorization.index.fiber k).card ≤
          P.branchingLoss * P.branching := by
    intro k hk
    exact P.fiber_card_le_loss_mul_branching k hk
  obtain ⟨A, b, hall⟩ :=
    exists_postAssembly_heavyParentLabel_bucket
      P.asConvexFactorization Y lambda L label
      hL0 hLtop hglobal hfiber (rho : ℝ) hrReal
      (P.branchingLoss * P.branching) hM
  dsimp only at hall
  obtain ⟨hparentsSubset, hretained, hwitness, hparentsOfMass,
    hpoint, houter, hfrozen, hfiberBound, hfiberConstant⟩ := hall
  have hparents := hparentsOfMass hmass0
  have hdensity :=
    lambda_div_loss_le_selected_neighborhoodDensity
      P
      (postHeavyRefinement P.asConvexFactorization A lambda L label b).shading
      (postHeavyParents P.asConvexFactorization A lambda L label b)
      hparents lambda
      (2 * amplifiedLoss P.asConvexFactorization
        (P.branchingLoss * P.branching) L)
      hwitness hdeltaPos hrhoPos P.scale_le hrhoHalf
  refine ⟨A, b, ?_⟩
  dsimp only
  exact ⟨hparentsSubset, hretained, hparents, hwitness,
    hpoint, houter, hfrozen, hfiberBound, hfiberConstant, hdensity⟩

end PostAssemblyTubeDensity

end

end Submission.Kakeya.ConvexFactoring
