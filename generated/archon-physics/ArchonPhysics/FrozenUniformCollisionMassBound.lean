import ArchonPhysics.CubicVertexInfraredBound
import ArchonPhysics.RandomMassPositiveCollisionData
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Uniform total-mass bound for the frozen three-wave collision data

For the frozen iid mass support `[4/5, 6/5]`, every harmonic frequency is at
most `sqrt 5`.  Combining this band edge with the deterministic acoustic
vertex estimate gives a realization-independent bound on each positive
three-wave interaction weight.  Averaging over all ordered triples therefore
gives the same bound on the total mass of the tuple-normalized collision
measure.

The simple-spectrum assumption is explicit: it is used only to identify the
basis-free ordered projector weight with the physical normal-mode vertex.
No thermodynamic limit, resonance-density statement, or kinetic conclusion is
asserted.
-/

namespace ArchonPhysics.FrozenUniformCollisionMassBound

open ArchonPhysics
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

noncomputable section

/-- Total normalized interaction weight of all ordered positive triples. -/
def positiveOrderedTotalInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      harmonicOrderedNormalizedInteractionWeight m modes
    else 0

/-- Tuple-averaged total normalized interaction weight. -/
def averagedPositiveOrderedTotalInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real :=
  (Fintype.card (OrderedModeTriple N) : Real)⁻¹ *
    positiveOrderedTotalInteractionWeight m

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every positive ordered triple in a frozen realization has uniformly
bounded physical normalized interaction weight. -/
theorem iid_harmonicOrderedNormalizedInteractionWeight_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega)))
    (modes : OrderedModeTriple N)
    (hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes) :
    harmonicOrderedNormalizedInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) modes ≤
      Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hphysical : PositiveModeTuple m
      (fun r ↦ orderedIndexEquiv (modes r)) :=
    (isPositiveOrderedTriple_iff_physical m modes).1 hpositive
  have hvertex := normalizedInteractionWeight_three_le m
    (fun r ↦ orderedIndexEquiv (modes r)) hphysical
  have hfrequency (r : Fin 3) :
      modeFrequency m (orderedIndexEquiv (modes r)) ≤ Real.sqrt 5 := by
    rw [← orderedModeFrequency_harmonicHermitian_eq]
    exact iid_orderedModeFrequency_harmonic_le_sqrt_five
      ensemble omega (modes r)
  have hfrequency_nonneg (r : Fin 3) :
      0 ≤ modeFrequency m (orderedIndexEquiv (modes r)) :=
    Real.sqrt_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hproduct :
      modeFrequency m (orderedIndexEquiv (modes 0)) *
          modeFrequency m (orderedIndexEquiv (modes 1)) *
          modeFrequency m (orderedIndexEquiv (modes 2)) ≤
        Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 := by
    exact mul_le_mul
      (mul_le_mul (hfrequency 0) (hfrequency 1)
        (hfrequency_nonneg 1) hsqrt_nonneg)
      (hfrequency 2) (hfrequency_nonneg 2)
      (mul_nonneg hsqrt_nonneg hsqrt_nonneg)
  rw [harmonicOrderedNormalizedInteractionWeight_eq m hsimple]
  exact hvertex.trans (div_le_div_of_nonneg_right hproduct (by norm_num))

/-- The total positive-triple weight is at most the number of ordered triples
times the same realization-independent constant. -/
theorem iid_positiveOrderedTotalInteractionWeight_le_card_mul
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    positiveOrderedTotalInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) ≤
      (Fintype.card (OrderedModeTriple N) : Real) *
        (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) := by
  classical
  unfold positiveOrderedTotalInteractionWeight
  calc
    (∑ modes : OrderedModeTriple N,
        if IsPositiveOrderedTriple
            (ensemble.restrictPositiveMass (N := N) omega) modes then
          harmonicOrderedNormalizedInteractionWeight
            (ensemble.restrictPositiveMass (N := N) omega) modes
        else 0) ≤
        ∑ _modes : OrderedModeTriple N,
          (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) := by
      apply Finset.sum_le_sum
      intro modes _hmodes
      by_cases hpositive : IsPositiveOrderedTriple
          (ensemble.restrictPositiveMass (N := N) omega) modes
      · rw [if_pos hpositive]
        exact iid_harmonicOrderedNormalizedInteractionWeight_le
          ensemble omega hsimple modes hpositive
      · rw [if_neg hpositive]
        positivity
    _ = (Fintype.card (OrderedModeTriple N) : Real) *
        (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8) := by simp

/-- After tuple normalization, the total collision weight is uniformly
bounded independently of system size and the mass realization. -/
theorem iid_averagedPositiveOrderedTotalInteractionWeight_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (ensemble.restrictPositiveMass (N := N) omega))) :
    averagedPositiveOrderedTotalInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) ≤
      Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8 := by
  let c : Real := Fintype.card (OrderedModeTriple N)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Fintype.card_pos
  have htotal := iid_positiveOrderedTotalInteractionWeight_le_card_mul
    ensemble omega hsimple
  unfold averagedPositiveOrderedTotalInteractionWeight
  change c⁻¹ * positiveOrderedTotalInteractionWeight
      (ensemble.restrictPositiveMass (N := N) omega) ≤ _
  calc
    c⁻¹ * positiveOrderedTotalInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) ≤
      c⁻¹ * (c * (Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8)) :=
        mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hc.le)
    _ = Real.sqrt 5 * Real.sqrt 5 * Real.sqrt 5 / 8 := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end

end ArchonPhysics.FrozenUniformCollisionMassBound
