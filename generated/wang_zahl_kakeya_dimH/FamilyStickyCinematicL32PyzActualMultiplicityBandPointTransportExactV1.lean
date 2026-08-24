import FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
import FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyE2SelectionV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualMultiplicityBandPointTransportExactV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyE2SelectionV1

noncomputable section

/-!
# Exact centered-half-cell to physical-band transport

The first PYZ selection supplies `base ⊆ physical.multiplicityBand`.  A
later positive-cardinality label cell is literally contained in `base`, so
its selected point remains in that physical band.  No cardinality comparison
is stored as source data.
-/

theorem q_mem_actualPhysical_multiplicityBand_of_centeredHalfCell
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent tangencyThreshold : Real)
    {lower upper : Nat} (label : Int) (q : Real × Real)
    (hbaseBand : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      base ⊆ physical.multiplicityBand lower upper)
    (hq : let Z :=
        (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
          fine ambient physicalBase hphysicalBase base hbase f hfContinuous
          f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          (36 * globalScale) tangencyExponent tangencyThreshold)
      q ∈ projectedPositiveMultiplicityDyadicCell Z label) :
    let physical :=
      (actualProjectedNormFirstSixteenthPhysicalShading fine ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB)
    q ∈ physical.multiplicityBand lower upper := by
  dsimp only at hbaseBand hq ⊢
  exact hbaseBand hq.1

#print axioms q_mem_actualPhysical_multiplicityBand_of_centeredHalfCell

end

end FamilyStickyCinematicL32PyzActualMultiplicityBandPointTransportExactV1
