import FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1
import FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstExtremalGlobalCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceExtremalCoefficientCapV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Extremal/c-bucket producer for the norm-first active cap

The low branch previously exposed a pointwise `hactiveCap` callback.  That
callback follows from the fixed Wang--Zahl `L₃` source chart, the ambient
half-radius `c`-bucket bound, the extremal same-scale cover, and its explicit
parallel-cluster loss budget.
-/

/-- Extremal and selected `c`-bucket data produce the entire coefficient cap
on the norm-first multiplicity band.  Pointwise pairwise distinctness and the
active cap itself are not inputs. -/
theorem activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal
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
    (hcBucket : ∀ i, i ∈ ambient → ∀ j, j ∈ ambient →
      |projectedTubeGraphC (S.family.tubes i) -
        projectedTubeGraphC (S.family.tubes j)| ≤ (radius : Real) / 2)
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
  let physical := actualProjectedNormFirstSixteenthPhysicalShading
    S.family ambient physicalBase hphysicalBase f hfContinuous A B
  have hphysicalAmbient : physical.ambient = ambient := rfl
  have hvertical : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).axis.direction 2 ≠ 0 := by
    intro i hi hzero
    have hhalf := S.source_direction_final_half i
      (hambient (by simpa only [hphysicalAmbient] using hi))
    rw [hzero, abs_zero] at hhalf
    norm_num at hhalf
  have hcBucketPhysical : ∀ i, i ∈ physical.ambient →
      ∀ j, j ∈ physical.ambient →
      |projectedTubeGraphC (S.family.tubes i) -
        projectedTubeGraphC (S.family.tubes j)| ≤ (radius : Real) / 2 := by
    intro i hi j hj
    apply hcBucket i
    · simpa only [hphysicalAmbient] using hi
    · simpa only [hphysicalAmbient] using hj
  exact activeNearCoefficientIndices_cap_on_band_of_extremal physical G
    hvertical hcBucketPhysical hloss

#print axioms activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal

end

end FamilyStickyCinematicL32PyzActualNormFirstExtremalGlobalCapV1
