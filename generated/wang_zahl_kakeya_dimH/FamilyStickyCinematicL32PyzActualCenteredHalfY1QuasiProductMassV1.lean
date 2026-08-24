import FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
import FamilyStickyCinematicL32PyzLowMultiplicityE2MomentSandwichV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

noncomputable section

/-!
# Quasi-product mass for the faithful centered-half `Y₁`

The physical carrier base and the selected tangency base are independent
arguments.  Only the selected base is required to lie in the quasi-product
source `E`; carrier containment is transported separately through the
physical shading.  Thus the mass estimate does not identify the two bases.
-/

def pyzActualCenteredHalfY1FrostmanPieceMass
    (radius : NNReal) (alpha : Real) (C : ENNReal) (A B : Real) : ENNReal :=
  (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha) *
      (ENNReal.ofReal (2 * (radius : Real))) ^ alpha) *
    (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha) *
      (ENNReal.ofReal
        (centeredFractionRight A B (1 / 16 : Real) -
          centeredFractionLeft A B (1 / 16 : Real))) ^ alpha)

theorem actualCenteredHalfY1_restrictedCarrier_subset_quasiProductStrip
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {E : Set (Real × Real)}
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (hbaseSubset : base ⊆ E)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (label : Int) (i : iota) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    pyzE2RestrictedCarrier Z label i ⊆
      E ∩ pyzCarrierGraphStrip
        (centeredFractionLeft A B (1 / 16 : Real))
        (centeredFractionRight A B (1 / 16 : Real))
        (projectedTubeCinematicTrace f (fine.tubes i)) (radius : Real) := by
  dsimp only
  intro q hq
  refine ⟨?_, ?_⟩
  · exact hbaseSubset hq.1.1
  · exact actualProjectedNormFirstSixteenthCenteredHalfY1_carrier_subset_strip
      fine ambient physicalBase hphysicalBase base hbase f hfContinuous f1 f2
      A B hAB hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold i hq.2

theorem volume_actualCenteredHalfY1_restrictedCarrier_le_frostmanPieceMass
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (hbaseSubset : base ⊆ E)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (label : Int) (i : iota) :
    let Z := actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
      hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
      tangencyExponent tangencyThreshold
    volume (pyzE2RestrictedCarrier Z label i) ≤
      pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
  dsimp only
  calc
    volume (pyzE2RestrictedCarrier
      (actualProjectedNormFirstSixteenthCenteredHalfY1 fine ambient
        physicalBase hphysicalBase base hbase f hfContinuous f1 f2 A B hAB
        hfDeriv hf1Deriv globalScale globalCenter tangencyCeiling
        tangencyExponent tangencyThreshold) label i) ≤
      volume (E ∩ pyzCarrierGraphStrip
        (centeredFractionLeft A B (1 / 16 : Real))
        (centeredFractionRight A B (1 / 16 : Real))
        (projectedTubeCinematicTrace f (fine.tubes i)) (radius : Real)) :=
      measure_mono
        (actualCenteredHalfY1_restrictedCarrier_subset_quasiProductStrip
          fine ambient physicalBase hphysicalBase base hbase hbaseSubset f
          hfContinuous f1 f2 A B hAB hfDeriv hf1Deriv globalScale
          globalCenter tangencyCeiling tangencyExponent tangencyThreshold
          label i)
    _ ≤ pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B := by
      simpa only [pyzActualCenteredHalfY1FrostmanPieceMass] using
        (volume_inter_pyzCarrierGraphStrip_le_frostmanProduct Q
          (a := centeredFractionLeft A B (1 / 16 : Real))
          (b := centeredFractionRight A B (1 / 16 : Real))
          (width := (radius : Real))
          (g := projectedTubeCinematicTrace f (fine.tubes i))
          (continuous_projectedTubeCinematicTrace f hfContinuous
            (fine.tubes i)).measurable)

end
end FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
