import «Family4FrozenDensityAdapter»

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4MinimalJoint

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open TubeSelectedFamilyRatioPrototype
open Family4FrozenDensityAdapter

noncomputable section

set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}

/-- The sole extra WZ extremal input.  `CoarseTubePartition` has no field
relating the chosen pointwise fiber bucket to the ratio `rho^2 / delta^2`. -/
def WZJointNormalization {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r) (Q : ℝ≥0∞) : Prop :=
  (rho : ℝ≥0∞) ^ 2 *
      ((2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
        A.fiberLabel : ℕ) : ℝ≥0∞) ≤
    Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2

/-- Items 1--6 on one actual formal assembly and its literal stored coarse
shading.  Unlike the existential convenience wrapper, joint normalization is
assumed only for this selected object. -/
theorem family4_items_one_to_six {r : ℝ}
    (A : Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly.Assembly
      P.asConvexFactorization Y r)
    (activeLoss : ℕ)
    (hactive : WithinFactor activeLoss Y.shadingMass
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingMass)
    (Q : ℝ≥0∞) (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹)
    (hjoint : WZJointNormalization A Q) :
    WithinFactor (activeLoss * A.loss) Y.shadingMass
        A.refinement.shading.shadingMass ∧
      A.refinement.shading.shadedUnion ⊆ A.frozenCoarse.shadedUnion ∧
      (∀ k ∈ P.coarseIndices, ∀ x ∈
        P.asConvexFactorization.fiberShadedUnion A.refinement.shading k,
        Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable
          (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
            A.fiberLabel)
          (P.asConvexFactorization.fiberMultiplicity A.refinement.shading k x)) ∧
      (∀ x ∈ A.frozenCoarse.shadedUnion,
        Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.ZeroOrComparable
          (Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
            A.outerLabel)
          (A.frozenCoarse.pointMultiplicity x)) ∧
      (∀ x, A.refinement.shading.pointMultiplicity x ≤
        A.frozenCoarse.pointMultiplicity x *
          (2 * Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets.comparableBase
            A.fiberLabel)) ∧
      (FrozenTubeDensityMasterPrototype.activeFineShading P Y).shadingDensity ≤
        16 * ((ofFrozenNeighborhoodAssembly A).loss : ℝ≥0∞) *
          (P.branchingLoss : ℝ≥0∞) * Q *
          (FrozenTubeDensityMasterPrototype.activeFrozenShading P
            (ofFrozenNeighborhoodAssembly A).frozenCoarse).shadingDensity := by
  refine ⟨source_retained A activeLoss hactive,
    A.shadedUnion_subset_frozenCoarse, A.fiber_comparable,
    A.outer_comparable, A.pointMultiplicity_le_frozenProduct, ?_⟩
  have hjoint' : (rho : ℝ≥0∞) ^ 2 *
      ((ofFrozenNeighborhoodAssembly A).fiberBound : ℝ≥0∞) ≤
        Q * (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 := by
    simpa [WZJointNormalization, ofFrozenNeighborhoodAssembly] using hjoint
  exact ((ofFrozenNeighborhoodAssembly A).density_lower_of_jointNormalization
    Q hdeltaPos hrhoHalf hjoint').1

end
end Family4MinimalJoint

#print axioms Family4MinimalJoint.WZJointNormalization
#print axioms Family4MinimalJoint.family4_items_one_to_six
