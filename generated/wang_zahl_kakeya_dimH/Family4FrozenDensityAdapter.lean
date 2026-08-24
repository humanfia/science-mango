import «FrozenTubeDensityMasterPrototype»
import «FrozenNeighborhoodAssemblyScratch»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4FrozenDensityAdapter

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open TubeSelectedFamilyRatioPrototype

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- The active tube shading is definitionally the shading of the formal
restriction refinement. -/
theorem activeFineShading_mass_eq_restrictTo
    (P : CoarseTubePartition fineFamily coarseFamily)
    (Y : Shading fineFamily.bodyFamily) :
    (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass =
      (IndexedShadingRefinement.restrictTo Y
        P.asConvexFactorization.index.fine).shading.shadingMass := by
  unfold FrozenTubeDensityMasterPrototype.activeFineShading activeFineBodyFamily
  rw [selectedCoarseShading_mass,
    shadingMass_restrictTo_eq_sum]
  rfl

/-- Convert the formal frozen-neighborhood output into the tube-density
assembly.  The stored `frozenCoarse` and refinement are reused literally. -/
def ofFrozenNeighborhoodAssembly {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly P.asConvexFactorization Y r) :
    FrozenTubeDensityMasterPrototype.Assembly P Y where
  refinement := A.refinement
  frozenCoarse := A.frozenCoarse
  loss := A.loss
  fiberBound := 2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase A.fiberLabel
  outerLabel := A.outerLabel
  indices_subset_fine := A.indices_subset_fine
  retained := by
    rw [activeFineShading_mass_eq_restrictTo]
    exact A.retained
  covers := A.covers
  fiber_bound := by
    intro k hk x hx
    simpa using A.fiberMultiplicity_le_twice_base k hk x
  outer_comparable := by
    intro x hx
    simpa [FrozenTubeDensityMasterPrototype.ZeroOrComparable, FrozenTubeDensityMasterPrototype.comparableBase,
      Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable, Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase] using
        A.outer_comparable x hx

/-- Inactive fine mass is not silently discarded.  This is the exact source
retention obtained by composing an explicit active-selection certificate with
the two comparable-multiplicity buckets. -/
theorem source_retained
    {r : ℝ} (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly P.asConvexFactorization Y r)
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass) :
    WithinFactor (activeLoss * A.loss) Y.shadingMass
      A.refinement.shading.shadingMass := by
  exact WithinFactor.trans hactive
    (by
      rw [activeFineShading_mass_eq_restrictTo]
      exact A.retained)

/-- All multiplicity and density conclusions concern the same frozen coarse
shading.  The only additional paper-facing numerical input is the joint
scale/fiber normalization. -/
theorem exists_family4_items_one_to_six
    (r : ℝ) (hr : 0 < r)
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass)
    (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hjoint : ∀ A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly P.asConvexFactorization Y r,
      (rho : ℝ≥0∞) ^ 2 *
          (2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase A.fiberLabel : ℕ) ≤
        Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :
    ∃ A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly P.asConvexFactorization Y r,
      let D := ofFrozenNeighborhoodAssembly A
      A.loss =
          (Nat.log 2 (Fintype.card ι) + 2) *
            (Nat.log 2 (Fintype.card κ) + 2) ∧
        A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 2) ∧
        A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card κ) + 2) ∧
        WithinFactor (activeLoss * A.loss) Y.shadingMass
          A.refinement.shading.shadingMass ∧
        A.refinement.shading.shadedUnion ⊆ A.frozenCoarse.shadedUnion ∧
        (∀ k ∈ P.coarseIndices, ∀ x ∈
          P.asConvexFactorization.fiberShadedUnion A.refinement.shading k,
          Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase A.fiberLabel)
            (P.asConvexFactorization.fiberMultiplicity
              A.refinement.shading k x)) ∧
        (∀ x ∈ A.frozenCoarse.shadedUnion,
          Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase A.outerLabel)
            (A.frozenCoarse.pointMultiplicity x)) ∧
        (∀ x, A.refinement.shading.pointMultiplicity x ≤
          A.frozenCoarse.pointMultiplicity x *
            (2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase A.fiberLabel)) ∧
        (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity ≤
          16 * (D.loss : ℝ≥0∞) * (P.branchingLoss : ℝ≥0∞) * Q *
            (FrozenTubeDensityMasterPrototype.activeFrozenShading P D.frozenCoarse).shadingDensity := by
  obtain ⟨A, hloss, hfiberLabel, houterLabel⟩ :=
    Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.exists_assembly P.asConvexFactorization Y r hr
  refine ⟨A, hloss, hfiberLabel, houterLabel,
    source_retained A activeLoss hactive,
    A.shadedUnion_subset_frozenCoarse, A.fiber_comparable,
    A.outer_comparable, A.pointMultiplicity_le_frozenProduct, ?_⟩
  exact ((ofFrozenNeighborhoodAssembly A).density_lower_of_jointNormalization
    Q hdeltaPos hrhoHalf (hjoint A)).1

end
end Family4FrozenDensityAdapter

#print axioms Family4FrozenDensityAdapter.ofFrozenNeighborhoodAssembly
#print axioms Family4FrozenDensityAdapter.source_retained
#print axioms Family4FrozenDensityAdapter.exists_family4_items_one_to_six
