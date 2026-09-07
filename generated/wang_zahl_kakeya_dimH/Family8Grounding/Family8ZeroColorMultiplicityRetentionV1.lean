import Family8Grounding.Family8ZeroColorShadingRetentionENNRealV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ZeroColorMultiplicityRetentionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open Family8ZeroColorShadingRetentionENNRealV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Average-multiplicity return from a retained zero-colour sample

The sampled shaded union is a subset of the source union.  Combining this
denominator monotonicity with the exact `2k` mass retention gives the
deterministic comparison used after applying `KatzTaoProperty` to the sampled
actual datum.
-/

theorem source_averageMultiplicity_le_two_mul_k_mul_zeroColorActualDatum
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) :
    D.shading.averageMultiplicity ≤
      ((2 * k : Nat) : ENNReal) *
        (zeroColorActualDatum D k omega).shading.averageMultiplicity := by
  let sampled := zeroColorActualDatum D k omega
  have hmass : D.shading.shadingMass ≤
      ((2 * k : Nat) : ENNReal) * sampled.shading.shadingMass :=
    shadingMass_le_two_mul_k_mul_of_toReal_div_le D k omega hretained
  have hunion : sampled.shading.shadedUnion ⊆ D.shading.shadedUnion :=
    restrictActualTubeDatum_shadedUnion_subset D (zeroColorSample k omega)
  unfold Shading.averageMultiplicity
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion ≤
        (((2 * k : Nat) : ENNReal) * sampled.shading.shadingMass) /
          volume D.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (((2 * k : Nat) : ENNReal) * sampled.shading.shadingMass) /
          volume sampled.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = ((2 * k : Nat) : ENNReal) *
          (sampled.shading.shadingMass /
            volume sampled.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms source_averageMultiplicity_le_two_mul_k_mul_zeroColorActualDatum

end
end Family8ZeroColorMultiplicityRetentionV1
