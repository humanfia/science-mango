import Mathlib.Tactic

/-!
# Card-free cancellation for the selected-outer canonical Delta

This module isolates the scalar cancellation behind the canonical global
Equation (45) coefficient.  Write

* `V` for the source ambient volume;
* `B` for the body-volume sum used to normalize the selected fine source;
* `Bside` for the body-volume sum of the retained outer subfamily; and
* `d` for the lower endpoint of its density band.

The fine-source Frostman coefficient has the literal form

`sourceKT * V * d⁻¹ * B⁻¹`.

Passing to the outer family contributes the density-band factor
`(2 * d) * d⁻¹`, while its canonical ambient density is bounded by
`Bside / V`.  The two legitimate inverse cancellations leave only
`Bside * B⁻¹ <= 1`; hence no cardinality of the occurrence set appears.

All quantities which are cancelled are assumed separately nonzero and
finite.  In particular, none of the proofs below uses field-style
cancellation across a possible `0` or `∞` value.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8SelectedOuterCanonicalDeltaScalarCancellationV1

/-- Exact normal form for the selected-outer canonical-Delta scalar.

The inverse of `d` occurring in the source coefficient is deliberately not
cancelled.  Only the second inverse, introduced by the outer density-band
transport, cancels the displayed factor `d`.
-/
theorem selectedOuterCanonicalDeltaScalar_eq
    (sourceKT V d B Bside : ENNReal)
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞) :
    ((sourceKT * V * d⁻¹ * B⁻¹) * (2 * d) * d⁻¹) *
        (Bside / V) =
      (2 * sourceKT * d⁻¹) * (Bside * B⁻¹) := by
  calc
    ((sourceKT * V * d⁻¹ * B⁻¹) * (2 * d) * d⁻¹) *
          (Bside / V) =
        ((2 * sourceKT * d⁻¹) * (Bside * B⁻¹)) *
          (V * V⁻¹) * (d * d⁻¹) := by
      rw [div_eq_mul_inv]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = (2 * sourceKT * d⁻¹) * (Bside * B⁻¹) := by
      rw [ENNReal.mul_inv_cancel hV0 hVTop,
        ENNReal.mul_inv_cancel hd0 hdTop]
      simp

/-- The card-free upper bound after the retained body-volume sum is compared
with the source normalization sum. -/
theorem selectedOuterCanonicalDeltaScalar_le_two_mul_sourceKT_mul_inv
    (sourceKT V d B Bside : ENNReal)
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hBside : Bside ≤ B) :
    ((sourceKT * V * d⁻¹ * B⁻¹) * (2 * d) * d⁻¹) *
        (Bside / V) ≤
      2 * sourceKT * d⁻¹ := by
  have hratio : Bside * B⁻¹ ≤ 1 := by
    calc
      Bside * B⁻¹ ≤ B * B⁻¹ := mul_le_mul' hBside le_rfl
      _ = 1 := ENNReal.mul_inv_cancel hB0 hBTop
  rw [selectedOuterCanonicalDeltaScalar_eq sourceKT V d B Bside
    hV0 hVTop hd0 hdTop]
  calc
    (2 * sourceKT * d⁻¹) * (Bside * B⁻¹) ≤
        (2 * sourceKT * d⁻¹) * 1 := mul_le_mul' le_rfl hratio
    _ = 2 * sourceKT * d⁻¹ := mul_one _

/-- Named-coefficient wrapper for direct use by the geometric assembly.

`ambientDensity` may be the literal `ambientFamilyVolumeDensity`.  An upper
bound by `Bside / V` is enough, so the application does not need to expose a
stronger equality than its selected-outer volume bookkeeping provides.
-/
theorem outerCF_mul_ambientDensity_le_two_mul_sourceKT_mul_inv
    (sourceKT V d B Bside sourceCF outerCF ambientDensity : ENNReal)
    (hV0 : V ≠ 0) (hVTop : V ≠ ∞)
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hBside : Bside ≤ B)
    (hsourceCF : sourceCF = sourceKT * V * d⁻¹ * B⁻¹)
    (houterCF : outerCF = sourceCF * (2 * d) * d⁻¹)
    (hambientDensity : ambientDensity ≤ Bside / V) :
    outerCF * ambientDensity ≤ 2 * sourceKT * d⁻¹ := by
  calc
    outerCF * ambientDensity ≤
        ((sourceKT * V * d⁻¹ * B⁻¹) * (2 * d) * d⁻¹) *
          (Bside / V) := by
      rw [houterCF, hsourceCF]
      exact mul_le_mul' le_rfl hambientDensity
    _ ≤ 2 * sourceKT * d⁻¹ :=
      selectedOuterCanonicalDeltaScalar_le_two_mul_sourceKT_mul_inv
        sourceKT V d B Bside hV0 hVTop hd0 hdTop hB0 hBTop hBside

#print axioms selectedOuterCanonicalDeltaScalar_eq
#print axioms
  selectedOuterCanonicalDeltaScalar_le_two_mul_sourceKT_mul_inv
#print axioms outerCF_mul_ambientDensity_le_two_mul_sourceKT_mul_inv

end Family8SelectedOuterCanonicalDeltaScalarCancellationV1
