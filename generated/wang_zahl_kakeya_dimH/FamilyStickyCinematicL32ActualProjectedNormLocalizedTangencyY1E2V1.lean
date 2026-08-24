import FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
import FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyY1E2V1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyY1E2AfterNormCoverV1

noncomputable section

/-!
# Actual `Y₁` and `E₂` after the norm-cover localization

This is the concrete Tube specialization of the faithful post-cover carrier.
The tangency maximizer runs on `F_B(x)`, not on the pre-cover family.  Every
carrier and multiplicity band remains a finite measurable incidence pattern.
-/

universe u v

/-- Literal actual Tube `Y₁` after fixing one global norm ball. -/
noncomputable def actualProjectedNormLocalizedTangencyY1
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube delta)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real) :
    FiniteProjectedShading point iota :=
  finiteIncidenceLocalizedTangencyY1 base hbase physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (fun i hi => physical.measurable_carrier i hi)
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter
    (actualProjectedTangencyDistance f f1 f2 A B hAB hfDeriv hf1Deriv)
    fine.tubes (delta : Real) tangencyCeiling tangencyExponent
    tangencyThreshold

/-- The active family of actual `Y₁` is the literal filter by those carriers. -/
theorem activeAtPoint_actualProjectedNormLocalizedTangencyY1
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube delta)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (x : point) :
    (actualProjectedNormLocalizedTangencyY1 base hbase fine physical
      f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
      tangencyCeiling tangencyExponent tangencyThreshold).activeAtPoint x =
      finiteIncidenceActiveAtPoint physical.ambient
        (fun i x => x ∈
          (actualProjectedNormLocalizedTangencyY1 base hbase fine physical
            f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
            tangencyCeiling tangencyExponent tangencyThreshold).carrier i) x :=
  rfl

/-- Literal actual post-cover multiplicity band `E₂`. -/
def actualProjectedNormLocalizedTangencyE2
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube delta)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (lower upper : Nat) : Set point :=
  (actualProjectedNormLocalizedTangencyY1 base hbase fine physical
    f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
    tangencyCeiling tangencyExponent tangencyThreshold).multiplicityBand
      lower upper

/-- `E₂` is measurable from the actual finite carrier events; no measurable
selector or measurable active-map premise appears. -/
theorem measurableSet_actualProjectedNormLocalizedTangencyE2
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set point) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily delta iota)
    (physical : FiniteProjectedShading point iota)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube delta)
    (tangencyCeiling tangencyExponent tangencyThreshold : Real)
    (lower upper : Nat) :
    MeasurableSet
      (actualProjectedNormLocalizedTangencyE2 base hbase fine physical
        f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
        tangencyCeiling tangencyExponent tangencyThreshold lower upper) := by
  exact FiniteProjectedShading.measurableSet_multiplicityBand
    (actualProjectedNormLocalizedTangencyY1 base hbase fine physical
      f f1 f2 A B hAB hfDeriv hf1Deriv globalScale globalCenter
      tangencyCeiling tangencyExponent tangencyThreshold)
    lower upper

#print axioms actualProjectedNormLocalizedTangencyY1
#print axioms activeAtPoint_actualProjectedNormLocalizedTangencyY1
#print axioms actualProjectedNormLocalizedTangencyE2
#print axioms measurableSet_actualProjectedNormLocalizedTangencyE2

end

end FamilyStickyCinematicL32ActualProjectedNormLocalizedTangencyY1E2V1
