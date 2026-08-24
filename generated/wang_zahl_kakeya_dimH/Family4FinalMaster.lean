import «Family4SourceDensity»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4FinalMaster

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open TubeSelectedFamilyRatioPrototype
open Family4FrozenDensityAdapter
open Family4MinimalJoint
open Family4SourceDensity

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- Named same-object conclusion for Family 4 items 1--6. -/
structure Conclusion {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (activeLoss : ℕ) (Q : ℝ≥0∞) : Prop where
  source_retained : WithinFactor (activeLoss * A.loss) Y.shadingMass
    A.refinement.shading.shadingMass
  covered_by_same_frozen :
    A.refinement.shading.shadedUnion ⊆ A.frozenCoarse.shadedUnion
  fiber_comparable : ∀ k ∈ P.coarseIndices, ∀ x ∈
      P.asConvexFactorization.fiberShadedUnion A.refinement.shading k,
    Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable
      (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
        A.fiberLabel)
      (P.asConvexFactorization.fiberMultiplicity A.refinement.shading k x)
  outer_comparable : ∀ x ∈ A.frozenCoarse.shadedUnion,
    Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable
      (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
        A.outerLabel) (A.frozenCoarse.pointMultiplicity x)
  comparable_product : ∀ x, A.refinement.shading.pointMultiplicity x ≤
    A.frozenCoarse.pointMultiplicity x *
      (2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
        A.fiberLabel)
  active_density_lower :
    (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity ≤
      16 * ((ofFrozenNeighborhoodAssembly A).loss : ℝ≥0∞) *
        (P.branchingLoss : ℝ≥0∞) * Q *
        (FrozenTubeDensityMasterPrototype.activeFrozenShading P
          (ofFrozenNeighborhoodAssembly A).frozenCoarse).shadingDensity
  source_density_lower : Y.shadingDensity ≤
    (activeLoss : ℝ≥0∞) *
      (16 * ((ofFrozenNeighborhoodAssembly A).loss : ℝ≥0∞) *
        (P.branchingLoss : ℝ≥0∞) * Q) *
      (FrozenTubeDensityMasterPrototype.activeFrozenShading P
        (ofFrozenNeighborhoodAssembly A).frozenCoarse).shadingDensity

/-- One theorem, one formal assembly, and literally one stored `frozenCoarse`.
The two explicit non-structural inputs are active-mass retention and the WZ
joint normalization for this selected assembly. -/
theorem family4_items_one_to_six_same_object {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass)
    (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hjoint : WZJointNormalization A Q) :
    Conclusion A activeLoss Q := by
  rcases Family4MinimalJoint.family4_items_one_to_six A activeLoss hactive Q
      hdeltaPos hrhoHalf hjoint with
    ⟨hretained, hcover, hfiber, houter, hproduct, hdensity⟩
  exact {
    source_retained := hretained
    covered_by_same_frozen := hcover
    fiber_comparable := hfiber
    outer_comparable := houter
    comparable_product := hproduct
    active_density_lower := hdensity
    source_density_lower :=
      sourceDensity_lower_sameFrozen A activeLoss hactive Q hdeltaPos
        hrhoHalf hjoint }

end
end Family4FinalMaster

#print axioms Family4FinalMaster.family4_items_one_to_six_same_object
