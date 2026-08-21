import Submission.Kakeya.ConvexFactoring.L2Union

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# The division-free analytic consequence of the Cordoba inequality

This file isolates the `ENNReal` algebra that turns the `L^2` estimate in
`L2Union` into a lower bound for the union, and records safe quotient-form
consequences. In particular, the only cancellation is performed under
explicit nonzero and finite hypotheses; the shading-level theorems discharge
those hypotheses using a zero-mass case split and the already-proved finiteness
of `shadingMass`.
-/

/-- Cancel a finite, nonzero mass from the abstract Cordoba estimate.

The multiplication order in the conclusion is deliberate: if the moment is
at most `Q * mass`, then the mass is at most `Q * unionVolume`.
-/
theorem le_factor_mul_of_sq_le_mul_and_moment_le
    {mass unionVolume moment Q : ℝ≥0∞}
    (hmass_zero : mass ≠ 0) (hmass_top : mass ≠ ∞)
    (hcordoba : mass ^ 2 ≤ unionVolume * moment)
    (hmoment : moment ≤ Q * mass) :
    mass ≤ Q * unionVolume := by
  apply (ENNReal.mul_le_mul_iff_left hmass_zero hmass_top).mp
  calc
    mass * mass = mass ^ 2 := by rw [pow_two]
    _ ≤ unionVolume * moment := hcordoba
    _ ≤ unionVolume * (Q * mass) := mul_le_mul' le_rfl hmoment
    _ = (Q * unionVolume) * mass := by ac_rfl

/-- Finite-mass wrapper around
`le_factor_mul_of_sq_le_mul_and_moment_le`, valid also when `mass = 0`. -/
theorem le_factor_mul_of_sq_le_mul_and_moment_le_of_lt_top
    {mass unionVolume moment Q : ℝ≥0∞}
    (hmass_top : mass < ∞)
    (hcordoba : mass ^ 2 ≤ unionVolume * moment)
    (hmoment : moment ≤ Q * mass) :
    mass ≤ Q * unionVolume := by
  rcases eq_or_ne mass 0 with hmass_zero | hmass_zero
  · simp [hmass_zero]
  · exact le_factor_mul_of_sq_le_mul_and_moment_le hmass_zero hmass_top.ne
      hcordoba hmoment

/-- Dividing the division-free conclusion by the union volume is always safe
in `ENNReal`; this formulation also covers zero and infinite union volume. -/
theorem average_le_factor_of_mass_le_factor_mul_unionVolume
    {mass unionVolume Q : ℝ≥0∞}
    (h : mass ≤ Q * unionVolume) :
    mass / unionVolume ≤ Q :=
  ENNReal.div_le_of_le_mul h

/-- A safe quotient-form lower bound for the union volume. No positivity or
finiteness assumption on `Q` is required. -/
theorem mass_div_factor_le_unionVolume_of_mass_le_factor_mul
    {mass unionVolume Q : ℝ≥0∞}
    (h : mass ≤ Q * unionVolume) :
    mass / Q ≤ unionVolume :=
  ENNReal.div_le_of_le_mul' h

/-- Dividing a mass bound by a reference volume gives the corresponding
density bound, with all `ENNReal` edge cases retained. -/
theorem density_le_factor_mul_unionRatio_of_mass_le_factor_mul
    {mass unionVolume referenceVolume Q : ℝ≥0∞}
    (h : mass ≤ Q * unionVolume) :
    mass / referenceVolume ≤ Q * (unionVolume / referenceVolume) := by
  calc
    mass / referenceVolume ≤ (Q * unionVolume) / referenceVolume :=
      ENNReal.div_le_div_right h referenceVolume
    _ = Q * (unionVolume / referenceVolume) := by
      simp only [div_eq_mul_inv, mul_assoc]

variable {iota : Type*} {F : ConvexFamily iota} (Y : Shading F)

/-- A second-moment bound by `Q` times shaded mass implies the division-free
union estimate `mass ≤ Q * unionVolume`. -/
theorem shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hsecond :
      (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
        Q * Y.shadingMass) :
    Y.shadingMass ≤ Q * volume Y.shadedUnion := by
  exact le_factor_mul_of_sq_le_mul_and_moment_le_of_lt_top
    Y.shadingMass_lt_top
    (shadingMass_sq_le_volume_shadedUnion_mul_secondMoment Y) hsecond

/-- The overlap-sum version of the division-free union estimate. -/
theorem shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hoverlap :
      (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Q * Y.shadingMass) :
    Y.shadingMass ≤ Q * volume Y.shadedUnion := by
  exact le_factor_mul_of_sq_le_mul_and_moment_le_of_lt_top
    Y.shadingMass_lt_top
    (shadingMass_sq_le_volume_shadedUnion_mul_overlapSum Y) hoverlap

/-- Safe average-multiplicity consequence of a second-moment upper bound. -/
theorem averageMultiplicity_le_factor_of_secondMoment_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hsecond :
      (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
        Q * Y.shadingMass) :
    Y.averageMultiplicity ≤ Q := by
  unfold Shading.averageMultiplicity
  exact average_le_factor_of_mass_le_factor_mul_unionVolume
    (shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le Y Q hsecond)

/-- Safe average-multiplicity consequence of an overlap-sum upper bound. -/
theorem averageMultiplicity_le_factor_of_overlapSum_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hoverlap :
      (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Q * Y.shadingMass) :
    Y.averageMultiplicity ≤ Q := by
  unfold Shading.averageMultiplicity
  exact average_le_factor_of_mass_le_factor_mul_unionVolume
    (shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y Q hoverlap)

/-- Safe quotient-form union-volume consequence of a second-moment bound. -/
theorem shadingMass_div_factor_le_volume_shadedUnion_of_secondMoment_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hsecond :
      (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
        Q * Y.shadingMass) :
    Y.shadingMass / Q ≤ volume Y.shadedUnion :=
  mass_div_factor_le_unionVolume_of_mass_le_factor_mul
    (shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le Y Q hsecond)

/-- Safe quotient-form union-volume consequence of an overlap-sum bound. -/
theorem shadingMass_div_factor_le_volume_shadedUnion_of_overlapSum_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hoverlap :
      (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Q * Y.shadingMass) :
    Y.shadingMass / Q ≤ volume Y.shadedUnion :=
  mass_div_factor_le_unionVolume_of_mass_le_factor_mul
    (shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y Q hoverlap)

/-- Density consequence of a second-moment bound. The right side is the
factor times the fraction of the family volume occupied by the shaded union. -/
theorem shadingDensity_le_factor_mul_unionRatio_of_secondMoment_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hsecond :
      (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
        Q * Y.shadingMass) :
    Y.shadingDensity ≤ Q * (volume Y.shadedUnion / familyVolume F) := by
  unfold Shading.shadingDensity
  exact density_le_factor_mul_unionRatio_of_mass_le_factor_mul
    (shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le Y Q hsecond)

/-- Density consequence of an overlap-sum bound. -/
theorem shadingDensity_le_factor_mul_unionRatio_of_overlapSum_le
    [Fintype iota] (Q : ℝ≥0∞)
    (hoverlap :
      (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        Q * Y.shadingMass) :
    Y.shadingDensity ≤ Q * (volume Y.shadedUnion / familyVolume F) := by
  unfold Shading.shadingDensity
  exact density_le_factor_mul_unionRatio_of_mass_le_factor_mul
    (shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y Q hoverlap)

end Submission.Kakeya.ConvexFactoring
