import ArchonPhysics.CouplingWeightedJacobianSpectralBudget

/-!
# Linear-volume bound for the ordered counterrotating static flux

The all-plus three-wave flux contains the three pairwise products of harmonic
actions.  Although one action is singular like `1 / omega` at the acoustic
edge, the exactly normalized cubic vertex contributes `omega / 2` on the same
leg.  The spectral-kernel factorization therefore bounds each pair sector by
one frequency ceiling and two energy ceilings, with only one volume factor.

This module proves the bound for the complete ordered positive-frequency
triple sum.  It is deliberately stronger than an all-distinct or fixed-output
subsum, and it uses no acoustic gap or tuple-cardinality estimate.
-/

namespace ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CouplingWeightedJacobianSpectralBudget
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open scoped BigOperators

noncomputable section

/-- Harmonic action in the canonical ordered-mode indexing. -/
def orderedModeAction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) (k : OrderedModeIndex N) : Real :=
  energy k / orderedModeFrequency (harmonicHermitian m) k

/-- One of the three pair-action factors: the `missing` leg contributes one,
and both remaining legs contribute their harmonic actions. -/
def pairActionEnvelope {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real)
    (missing r : Fin 3) (k : OrderedModeIndex N) : Real :=
  if r = missing then 1 else orderedModeAction m energy k

/-- The all-plus collision bracket, written symmetrically as the sum over the
three choices of the leg missing from a pair-action product. -/
def orderedAllPlusActionFlux {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real)
    (modes : OrderedModeTriple N) : Real :=
  ∑ missing : Fin 3, ∏ r : Fin 3,
    pairActionEnvelope m energy missing r (modes r)

/-- Complete positive-frequency collision-weighted all-plus action flux. -/
def positiveOrderedAllPlusActionFluxSum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) : Real :=
  positiveCouplingWeightedTupleSum m
    (orderedAllPlusActionFlux m energy)

/-- The positive-frequency indicator times one harmonic action has a bounded
effective spectral weight.  This is the exact acoustic cancellation:
`(omega / 2) * (energy / omega) = energy / 2`. -/
theorem abs_activeNormalized_positiveAction_le_half_energyCeiling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) (energyCeiling : Real)
    (henergyNonneg : ∀ k, 0 ≤ energy k)
    (henergy : ∀ k, energy k ≤ energyCeiling)
    (k : OrderedModeIndex N) :
    |activeNormalizedIndicatorEffectiveWeight m
      (fun q ↦ orderedPositiveFrequencyIndicator m q *
        orderedModeAction m energy q) k| ≤ energyCeiling / 2 := by
  classical
  let omega := orderedModeFrequency (harmonicHermitian m) k
  by_cases hpositive : 0 < omega
  · have hbase := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
    have hactionNonneg : 0 ≤ orderedModeAction m energy k :=
      div_nonneg (henergyNonneg k) hpositive.le
    have haction : orderedModeAction m energy k ≤ energyCeiling / omega :=
      div_le_div_of_nonneg_right (henergy k) hpositive.le
    have henergyCeilingNonneg : 0 ≤ energyCeiling :=
      (henergyNonneg k).trans (henergy k)
    rw [activeNormalizedIndicatorEffectiveWeight,
      orderedPositiveFrequencyIndicator, if_pos hpositive, one_mul]
    change |activeOrderedEigenvalue m k *
        orderedModeAction m energy k * (2 * omega)⁻¹| ≤ _
    calc
      |activeOrderedEigenvalue m k * orderedModeAction m energy k *
          (2 * omega)⁻¹| =
          |activeOrderedEigenvalue m k * (2 * omega)⁻¹| *
            |orderedModeAction m energy k| := by
              simp only [abs_mul]
              ring
      _ ≤ (omega / 2) * (energyCeiling / omega) := by
        rw [abs_of_nonneg hactionNonneg]
        exact mul_le_mul hbase haction hactionNonneg
          (div_nonneg hpositive.le (by norm_num))
      _ = energyCeiling / 2 := by
        field_simp [hpositive.ne']
  · have henergyCeilingNonneg : 0 ≤ energyCeiling :=
      (henergyNonneg k).trans (henergy k)
    have hnot : ¬ 0 < orderedModeFrequency (harmonicHermitian m) k := by
      simpa [omega] using hpositive
    have hrhs : 0 ≤ energyCeiling / 2 :=
      div_nonneg henergyCeilingNonneg (by norm_num)
    unfold activeNormalizedIndicatorEffectiveWeight
      orderedPositiveFrequencyIndicator
    change |activeOrderedEigenvalue m k *
        ((if 0 < orderedModeFrequency (harmonicHermitian m) k then 1 else 0) *
          orderedModeAction m energy k) *
        (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹| ≤ _
    rw [if_neg hnot, zero_mul]
    simpa using hrhs

/-- A single pair-action sector has a volume-normalized bound
`frequencyCeiling * energyCeiling^2 / 8`. -/
theorem positiveCouplingWeighted_pairAction_div_volume_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real)
    (energyCeiling frequencyCeiling : Real)
    (henergyNonneg : ∀ k, 0 ≤ energy k)
    (henergy : ∀ k, energy k ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling)
    (missing : Fin 3) :
    positiveCouplingWeightedTupleSum m
        (fun modes ↦ ∏ r : Fin 3,
          pairActionEnvelope m energy missing r (modes r)) /
        (N : Real) ≤
      frequencyCeiling * energyCeiling ^ 2 / 8 := by
  let envelope : Fin 3 → OrderedModeIndex N → Real :=
    pairActionEnvelope m energy missing
  let bound : Fin 3 → Real := fun r ↦
    if r = missing then frequencyCeiling / 2 else energyCeiling / 2
  have henergyCeilingNonneg : 0 ≤ energyCeiling :=
    (henergyNonneg (default : OrderedModeIndex N)).trans
      (henergy (default : OrderedModeIndex N))
  have hboundNonneg : ∀ r, 0 ≤ bound r := by
    intro r
    by_cases hr : r = missing
    · simp [bound, hr, div_nonneg hfrequencyCeiling]
    · simp [bound, hr, div_nonneg henergyCeilingNonneg]
  have heffective : ∀ r k,
      |activeNormalizedIndicatorEffectiveWeight m
        (positiveSeparableLegWeight m envelope r) k| ≤ bound r := by
    intro r k
    by_cases hr : r = missing
    · subst r
      have hunit := abs_activeNormalized_positiveEnvelope_le
        m (fun _ ↦ (1 : Real)) 1 (by norm_num) (by simp)
        frequencyCeiling hfrequencyCeiling hfrequency k
      have henvelopeUnit :
          positiveSeparableLegWeight m envelope missing =
            fun q ↦ orderedPositiveFrequencyIndicator m q := by
        funext q
        simp [positiveSeparableLegWeight, envelope, pairActionEnvelope]
      have hboundMissing : bound missing = frequencyCeiling / 2 := by
        simp [bound]
      rw [henvelopeUnit, hboundMissing]
      simpa using hunit
    · have haction :=
        abs_activeNormalized_positiveAction_le_half_energyCeiling
          m energy energyCeiling henergyNonneg henergy k
      have henvelopeAction :
          positiveSeparableLegWeight m envelope r =
            fun q ↦ orderedPositiveFrequencyIndicator m q *
              orderedModeAction m energy q := by
        funext q
        simp [positiveSeparableLegWeight, envelope, pairActionEnvelope, hr]
      have hboundAction : bound r = energyCeiling / 2 := by
        simp [bound, hr]
      rw [henvelopeAction, hboundAction]
      exact haction
  have hmain := positiveCouplingWeightedTupleSum_div_volume_le_of_separable
    m
    (fun modes ↦ ∏ r : Fin 3,
      pairActionEnvelope m energy missing r (modes r))
    envelope
    (by
      intro modes _hpositive
      exact le_rfl)
    bound hboundNonneg heffective
  fin_cases missing
  · dsimp [bound] at hmain
    calc
      _ ≤ frequencyCeiling / 2 * (energyCeiling / 2) *
          (energyCeiling / 2) := hmain
      _ = frequencyCeiling * energyCeiling ^ 2 / 8 := by ring
  · dsimp [bound] at hmain
    calc
      _ ≤ energyCeiling / 2 * (frequencyCeiling / 2) *
          (energyCeiling / 2) := hmain
      _ = frequencyCeiling * energyCeiling ^ 2 / 8 := by ring
  · dsimp [bound] at hmain
    calc
      _ ≤ energyCeiling / 2 * (energyCeiling / 2) *
          (frequencyCeiling / 2) := hmain
      _ = frequencyCeiling * energyCeiling ^ 2 / 8 := by ring

/-- Linearity of the positive collision-weighted sum in the all-plus flux. -/
theorem positiveOrderedAllPlusActionFluxSum_eq_sum_pairAction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real) :
    positiveOrderedAllPlusActionFluxSum m energy =
      ∑ missing : Fin 3,
        positiveCouplingWeightedTupleSum m
          (fun modes ↦ ∏ r : Fin 3,
            pairActionEnvelope m energy missing r (modes r)) := by
  classical
  unfold positiveOrderedAllPlusActionFluxSum orderedAllPlusActionFlux
    positiveCouplingWeightedTupleSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp only [if_pos hpositive, Finset.mul_sum]
  · simp [hpositive]

/-- The complete ordered all-plus static action flux grows at most linearly
with the number of sites. -/
theorem positiveOrderedAllPlusActionFluxSum_div_volume_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : OrderedModeIndex N → Real)
    (energyCeiling frequencyCeiling : Real)
    (henergyNonneg : ∀ k, 0 ≤ energy k)
    (henergy : ∀ k, energy k ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    positiveOrderedAllPlusActionFluxSum m energy / (N : Real) ≤
      3 * (frequencyCeiling * energyCeiling ^ 2 / 8) := by
  rw [positiveOrderedAllPlusActionFluxSum_eq_sum_pairAction,
    Finset.sum_div]
  calc
    (∑ missing : Fin 3,
        positiveCouplingWeightedTupleSum m
          (fun modes ↦ ∏ r : Fin 3,
            pairActionEnvelope m energy missing r (modes r)) /
          (N : Real)) ≤
        ∑ _missing : Fin 3,
          frequencyCeiling * energyCeiling ^ 2 / 8 := by
      exact Finset.sum_le_sum fun missing _ ↦
        positiveCouplingWeighted_pairAction_div_volume_le
          m energy energyCeiling frequencyCeiling henergyNonneg henergy
          hfrequencyCeiling hfrequency missing
    _ = 3 * (frequencyCeiling * energyCeiling ^ 2 / 8) := by simp

/-- Including the physical factor `4 * kappa^2`, the per-volume static mass
is bounded by `(3/2) * kappa^2 * frequencyCeiling * energyCeiling^2`. -/
theorem four_kappa_sq_mul_positiveOrderedAllPlusActionFluxSum_div_volume_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : OrderedModeIndex N → Real)
    (energyCeiling frequencyCeiling : Real)
    (henergyNonneg : ∀ k, 0 ≤ energy k)
    (henergy : ∀ k, energy k ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    (4 * kappa ^ 2 * positiveOrderedAllPlusActionFluxSum m energy) /
        (N : Real) ≤
      (3 / 2 : Real) * kappa ^ 2 * frequencyCeiling *
        energyCeiling ^ 2 := by
  have hmain := positiveOrderedAllPlusActionFluxSum_div_volume_le
    m energy energyCeiling frequencyCeiling henergyNonneg henergy
    hfrequencyCeiling hfrequency
  have hkappa : 0 ≤ 4 * kappa ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg kappa)
  have hscaled := mul_le_mul_of_nonneg_left hmain hkappa
  calc
    (4 * kappa ^ 2 * positiveOrderedAllPlusActionFluxSum m energy) /
        (N : Real) =
      (4 * kappa ^ 2) *
        (positiveOrderedAllPlusActionFluxSum m energy / (N : Real)) := by ring
    _ ≤ (4 * kappa ^ 2) *
        (3 * (frequencyCeiling * energyCeiling ^ 2 / 8)) := hscaled
    _ = (3 / 2 : Real) * kappa ^ 2 * frequencyCeiling *
        energyCeiling ^ 2 := by ring

end

end ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound
