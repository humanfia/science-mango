import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedSourceAmbientDistinctSelectionV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

noncomputable section

universe u

/-!
# Public extremal inputs for the norm-first branch

The primitive extremal record, source containment, one concrete projected
half-radius `c`-bucket, and the explicit cover loss supply all distinctness
and active-cap inputs used by the norm-first branch.
-/

/-- The public extremal data simultaneously give ambient essential
distinctness, its restriction to every point of the norm-first multiplicity
band, and the whole-band active coefficient cap. -/
theorem actualNormFirst_public_inputs_of_extremal_bucket
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
    Set.Pairwise (ambient : Set iota) (fun i j =>
        EssentiallyDistinct (S.family.tubes i) (S.family.tubes j)) ∧
      (∀ x, x ∈ physical.multiplicityBand lower upper →
        Set.Pairwise (physical.activeAtPoint x : Set iota) (fun i j =>
          EssentiallyDistinct (S.family.tubes i) (S.family.tubes j))) ∧
      (∀ x, x ∈ physical.multiplicityBand lower upper →
        ∀ center,
          center ∈ actualProjectedCriticalFamily S.family
            (physical.activeAtPoint x) →
          (activeNearCoefficientIndices S.family (physical.activeAtPoint x)
            center (radius : Real)).card ≤ multiplicity) := by
  let physical := actualProjectedNormFirstSixteenthPhysicalShading
    S.family ambient physicalBase hphysicalBase f hfContinuous A B
  have hphysicalAmbient : physical.ambient = ambient := rfl
  have hambientPairwise : Set.Pairwise (ambient : Set iota) (fun i j =>
      EssentiallyDistinct (S.family.tubes i) (S.family.tubes j)) :=
    G.essentially_distinct
  have hbandPairwise : ∀ x, x ∈ physical.multiplicityBand lower upper →
      Set.Pairwise (physical.activeAtPoint x : Set iota) (fun i j =>
        EssentiallyDistinct (S.family.tubes i) (S.family.tubes j)) := by
    have hpointwise := essentiallyDistinct_activeAtPoint_of_ambient
      S.family physical (by simpa only [hphysicalAmbient] using hambientPairwise)
    exact fun x _hx => hpointwise x
  have hactiveCap : ∀ x, x ∈ physical.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint x) →
        (activeNearCoefficientIndices S.family (physical.activeAtPoint x)
          center (radius : Real)).card ≤ multiplicity := by
    exact activeNearCoefficientIndices_cap_on_actualNormFirst_band_of_extremal_bucket
      S ambient hambient physicalBase hphysicalBase f hfContinuous A B G
        bucket hbucket hloss
  exact ⟨hambientPairwise, hbandPairwise, hactiveCap⟩

#print axioms actualNormFirst_public_inputs_of_extremal_bucket

end

end FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
