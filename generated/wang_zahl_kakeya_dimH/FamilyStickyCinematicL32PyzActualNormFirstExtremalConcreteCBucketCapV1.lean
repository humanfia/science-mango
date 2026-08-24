import FamilyStickyCinematicL32PyzActualNormFirstExtremalGlobalCapV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalGlobalCapV1

noncomputable section

universe u

/-!
# Concrete floor-bucket producer for the norm-first active cap

This module keeps the bucket on the same projected graph-coordinate stack as
the actual low branch.  Equality of the literal floor-grid labels proves the
ambient `c`-slope bound, so the public endpoint no longer needs either an
`hcBucket` callback or an `hactiveCap` callback.
-/

/-- The actual projected `c`-coordinate floor bucket of width `eta`. -/
def actualProjectedTubeCBucket {radius : NNReal}
    (eta : Real) (T : Tube radius) : Int :=
  Int.floor (projectedTubeGraphC T / eta)

/-- Equality of positive-width actual projected buckets gives the required
non-strict slope separation. -/
theorem abs_projectedTubeGraphC_sub_le_of_bucket_eq
    {radius : NNReal} {eta : Real} (heta : 0 < eta)
    {T U : Tube radius}
    (hbucket : actualProjectedTubeCBucket eta T =
      actualProjectedTubeCBucket eta U) :
    |projectedTubeGraphC T - projectedTubeGraphC U| ≤ eta := by
  have hscaled :
      |projectedTubeGraphC T / eta - projectedTubeGraphC U / eta| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hbucket
  rw [← sub_div, abs_div, abs_of_pos heta] at hscaled
  exact ((div_lt_one heta).mp hscaled).le

/-- A single concrete half-radius bucket plus the primitive extremal record
produces the whole band-global active coefficient cap. -/
theorem activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal_bucket
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f) (A B : Real)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    {lower upper multiplicity : Nat}
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous A B
    ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices S.family (physical.activeAtPoint x)
          center (radius : Real)).card ≤ multiplicity := by
  apply activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal
    S ambient hambient physicalBase hphysicalBase f hfContinuous A B G
  · intro i hi j hj
    have hradiusReal : (0 : Real) < (radius : Real) := by
      exact_mod_cast G.delta_pos
    exact abs_projectedTubeGraphC_sub_le_of_bucket_eq
      (div_pos hradiusReal (by norm_num))
      ((hbucket i hi).trans (hbucket j hj).symm)
  · exact hloss

#print axioms abs_projectedTubeGraphC_sub_le_of_bucket_eq
#print axioms activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal_bucket

end

end FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
