import ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
import ArchonPhysics.LocalCollisionDensityTransfer

/-!
# Quantitative decay of the normalized sinc-squared kernel off resonance

The normalized finite-time resonance kernel has unit mass but peak height of
order `T`.  Consequently, an unweighted small-mass estimate does not control a
bad region uniformly in time.  If the mismatch stays at least `eta > 0` away
from zero, however, the exact sinc-squared tail gives the quantitative bound

`2 / (pi * T * eta^2)`.

This module lifts that pointwise estimate to arbitrary measures, supplies a
restriction form for a measurable bad set, and specializes it to the exact
weighted bad remainder used by `ActualThreeMassLiftedWeightedGoodBad`.
-/

namespace ArchonPhysics.NormalizedResonanceBadRegionDecay

open Filter MeasureTheory Set
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open scoped ENNReal Topology

noncomputable section

/-- The normalized sinc-squared density pulled back by an arbitrary mismatch
map. -/
def normalizedResonanceKernelDensity {X : Type*}
    (mismatch : X -> Real) (T : Real) (x : X) : ENNReal :=
  ENNReal.ofReal (normalizedFiniteTimeResonanceKernel (mismatch x) T)

/-- The repository's off-gap coefficient is exactly the explicit
`2 / (pi * T * eta^2)` tail constant. -/
theorem offGapCoefficient_eq_two_div_pi_mul_time_mul_sq
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T) :
    offGapCoefficient eta T = 2 / (Real.pi * T * eta ^ 2) := by
  unfold offGapCoefficient
  field_simp [ne_of_gt heta, ne_of_gt hT, Real.pi_ne_zero]

/-- A mismatch gap holding almost everywhere bounds the total normalized
kernel-weighted mass by the exact off-gap coefficient times the original
mass.  Finiteness is not needed at a fixed time. -/
theorem withDensity_normalizedResonanceKernelDensity_univ_le_offGap
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (mismatch : X -> Real) {eta T : Real}
    (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ᵐ x ∂mu, eta <= |mismatch x|) :
    mu.withDensity (normalizedResonanceKernelDensity mismatch T) univ <=
      ENNReal.ofReal (offGapCoefficient eta T) * mu univ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ x, normalizedResonanceKernelDensity mismatch T x ∂mu) <=
        ∫⁻ _x : X, ENNReal.ofReal (offGapCoefficient eta T) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hgap] with x hx
      exact ENNReal.ofReal_le_ofReal
        (normalizedFiniteTimeResonanceKernel_le_offGapCoefficient
          heta hT hx)
    _ = ENNReal.ofReal (offGapCoefficient eta T) * mu univ := by
      simp

/-- Measurable-set form of the bad-region estimate.  The mismatch gap only
has to hold on `bad`, and the right side uses the unweighted bad mass. -/
theorem restrict_withDensity_normalizedResonanceKernelDensity_univ_le_offGap
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (mismatch : X -> Real) {bad : Set X} (hbad : MeasurableSet bad)
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ x ∈ bad, eta <= |mismatch x|) :
    (mu.restrict bad).withDensity
        (normalizedResonanceKernelDensity mismatch T) univ <=
      ENNReal.ofReal (offGapCoefficient eta T) * mu bad := by
  have hgapAE : ∀ᵐ x ∂mu.restrict bad,
      eta <= |mismatch x| :=
    ae_restrict_of_forall_mem hbad hgap
  simpa using
    (withDensity_normalizedResonanceKernelDensity_univ_le_offGap
      (mu.restrict bad) mismatch heta hT hgapAE)

/-- Fully expanded restriction estimate with the explicit normalized
`2 / (pi * T * eta^2)` coefficient. -/
theorem restrict_withDensity_normalizedResonanceKernelDensity_univ_le_explicit
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (mismatch : X -> Real) {bad : Set X} (hbad : MeasurableSet bad)
    {eta T : Real} (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ x ∈ bad, eta <= |mismatch x|) :
    (mu.restrict bad).withDensity
        (normalizedResonanceKernelDensity mismatch T) univ <=
      ENNReal.ofReal (2 / (Real.pi * T * eta ^ 2)) * mu bad := by
  rw [<- offGapCoefficient_eq_two_div_pi_mul_time_mul_sq heta hT]
  exact restrict_withDensity_normalizedResonanceKernelDensity_univ_le_offGap
    mu mismatch hbad heta hT hgap

/-- Along any time scale tending to infinity, an off-resonance weighted mass
vanishes.  Finiteness is used precisely to rule out the indeterminate product
`0 * infinity` on the comparison side. -/
theorem tendsto_withDensity_normalizedResonanceKernelDensity_univ_zero
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (mismatch : X -> Real) {eta : Real} (heta : 0 < eta)
    (time : Nat -> Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hgap : ∀ᵐ x ∂mu, eta <= |mismatch x|) :
    Tendsto
      (fun n => mu.withDensity
        (normalizedResonanceKernelDensity mismatch (time n)) univ)
      atTop (nhds 0) := by
  have hcoefficientReal : Tendsto
      (fun n => offGapCoefficient eta (time n)) atTop (nhds 0) := by
    have hdiv := htime.const_div_atTop ((2 / eta) ^ 2)
    have hscaled := hdiv.mul_const ((2 * Real.pi)⁻¹)
    simpa [offGapCoefficient, div_eq_mul_inv, mul_assoc] using hscaled
  have hcoefficient : Tendsto
      (fun n => ENNReal.ofReal (offGapCoefficient eta (time n)))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hcoefficientReal
  have hupper : Tendsto
      (fun n => ENNReal.ofReal (offGapCoefficient eta (time n)) * mu univ)
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.mul_const hcoefficient
      (Or.inr (measure_ne_top mu univ))
    simpa using hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0) from
      tendsto_const_nhds) hupper (fun _ => bot_le) (fun n =>
        withDensity_normalizedResonanceKernelDensity_univ_le_offGap
          mu mismatch heta (htime_pos n) hgap)

/-- Restriction-level vanishing theorem for a fixed measurable bad set. -/
theorem tendsto_restrict_withDensity_normalizedResonanceKernelDensity_univ_zero
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (mismatch : X -> Real) {bad : Set X} (hbad : MeasurableSet bad)
    {eta : Real} (heta : 0 < eta)
    (time : Nat -> Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hgap : ∀ x ∈ bad, eta <= |mismatch x|) :
    Tendsto
      (fun n => (mu.restrict bad).withDensity
        (normalizedResonanceKernelDensity mismatch (time n)) univ)
      atTop (nhds 0) := by
  have hgapAE : ∀ᵐ x ∂mu.restrict bad,
      eta <= |mismatch x| :=
    ae_restrict_of_forall_mem hbad hgap
  exact tendsto_withDensity_normalizedResonanceKernelDensity_univ_zero
    (mu.restrict bad) mismatch heta time htime_pos htime hgapAE

/-- Direct estimate for the precise lifted weighted-bad remainder occurring
in `ActualThreeMassLiftedWeightedGoodBad`. -/
theorem liftedResonanceKernelDensity_weightedBad_le_offGap
    (badLifted : Measure MassTriple) {eta T : Real}
    (heta : 0 < eta) (hT : 0 < T)
    (hgap : ∀ᵐ value ∂badLifted, eta <= |value.2|) :
    badLifted.withDensity (liftedResonanceKernelDensity T) univ <=
      ENNReal.ofReal (offGapCoefficient eta T) * badLifted univ := by
  simpa [liftedResonanceKernelDensity,
    normalizedResonanceKernelDensity] using
    (withDensity_normalizedResonanceKernelDensity_univ_le_offGap
      badLifted Prod.snd heta hT hgap)

/-- The actual lifted weighted-bad remainder tends to zero whenever its
mismatch is uniformly separated from zero and its measure is finite. -/
theorem tendsto_liftedResonanceKernelDensity_weightedBad_zero
    (badLifted : Measure MassTriple) [IsFiniteMeasure badLifted]
    {eta : Real} (heta : 0 < eta)
    (time : Nat -> Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hgap : ∀ᵐ value ∂badLifted, eta <= |value.2|) :
    Tendsto
      (fun n => badLifted.withDensity
        (liftedResonanceKernelDensity (time n)) univ)
      atTop (nhds 0) := by
  simpa [liftedResonanceKernelDensity,
    normalizedResonanceKernelDensity] using
    (tendsto_withDensity_normalizedResonanceKernelDensity_univ_zero
      badLifted Prod.snd heta time htime_pos htime hgap)

end

end ArchonPhysics.NormalizedResonanceBadRegionDecay
