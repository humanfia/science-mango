import ArchonPhysics.KineticObservableBridge
import ArchonPhysics.R32FrozenEnergyDilution

/-!
# R32 late-window normalization stability

This module packages the deterministic normalization step needed by the R32
campaign.  A raw modal-energy `l1` estimate and a positive lower bound on the
reference total energy give a normalized estimate with the same bound,
multiplied by `2 / energyFloor`.  The assumptions and conclusion are uniform
over an arbitrary set of window endpoints.

The R32 specialization takes the reference profile to be the frozen
two-band, quarter-contrast profile.  Since that profile has total energy one
and is at `l1` distance at least `1 / 8` from positive-mode uniformity, raw
late-window closeness to it yields an explicit lower bound on the normalized
late-window distance from equipartition.

No dynamical approximation, probability estimate, or persistence claim is
asserted here: the raw closeness and energy floor remain explicit premises.
-/

namespace ArchonPhysics.R32LateWindowNormalizationStability

open Set
open ArchonPhysics
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.KineticObservableBridge
open ArchonPhysics.NormalizedL1Stability
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.R32FrozenEnergyDilution

noncomputable section

/-! ## Uniform normalization on a set of window endpoints -/

/-- Raw late-window `l1` closeness, a uniform positive total-energy floor,
and positivity of the comparison profile imply normalized closeness at every
endpoint in the same set.  The set of endpoints is arbitrary, so this theorem
does not hide any compactness or supremum argument. -/
theorem normalized_lateWindow_l1Distance_uniform_in_endpoint
    {Mode : Type} [Fintype Mode]
    (microscopic kinetic : Real -> Mode -> Real)
    (mu : Real) (endpoints : Set Real)
    (energyFloor rawError : Real)
    (hfloor : 0 < energyFloor)
    (hmicroscopicFloor : forall T, T ∈ endpoints ->
      energyFloor <=
        totalWeight (lateWindowAverage microscopic mu T))
    (hkineticTotal : forall T, T ∈ endpoints ->
      0 < totalWeight (lateWindowAverage kinetic mu T))
    (hkineticNonneg : forall T, T ∈ endpoints -> forall mode,
      0 <= lateWindowAverage kinetic mu T mode)
    (hraw : forall T, T ∈ endpoints ->
      l1Distance (lateWindowAverage microscopic mu T)
        (lateWindowAverage kinetic mu T) <= rawError) :
    forall T, T ∈ endpoints ->
      l1Distance
          (normalizedWeights (lateWindowAverage microscopic mu T))
          (normalizedWeights (lateWindowAverage kinetic mu T)) <=
        (2 / energyFloor) * rawError := by
  intro T hT
  calc
    l1Distance
        (normalizedWeights (lateWindowAverage microscopic mu T))
        (normalizedWeights (lateWindowAverage kinetic mu T)) <=
        (2 / energyFloor) *
          l1Distance (lateWindowAverage microscopic mu T)
            (lateWindowAverage kinetic mu T) :=
      l1Distance_normalizedWeights_le_of_lowerBound
        (lateWindowAverage microscopic mu T)
        (lateWindowAverage kinetic mu T)
        hfloor (hmicroscopicFloor T hT) (hkineticTotal T hT)
        (hkineticNonneg T hT)
    _ <= (2 / energyFloor) * rawError := by
      exact mul_le_mul_of_nonneg_left (hraw T hT) (by positivity)

/-- The same endpoint-uniform normalization estimate for profiles which have
already been averaged over their late windows.  This form is convenient when
the analytic layer exports the raw window profile directly. -/
theorem normalized_windowProfile_l1Distance_uniform_in_endpoint
    {Mode : Type} [Fintype Mode]
    (microscopicWindow kineticWindow : Real -> Mode -> Real)
    (endpoints : Set Real) (energyFloor rawError : Real)
    (hfloor : 0 < energyFloor)
    (hmicroscopicFloor : forall T, T ∈ endpoints ->
      energyFloor <= totalWeight (microscopicWindow T))
    (hkineticTotal : forall T, T ∈ endpoints ->
      0 < totalWeight (kineticWindow T))
    (hkineticNonneg : forall T, T ∈ endpoints -> forall mode,
      0 <= kineticWindow T mode)
    (hraw : forall T, T ∈ endpoints ->
      l1Distance (microscopicWindow T) (kineticWindow T) <= rawError) :
    forall T, T ∈ endpoints ->
      l1Distance (normalizedWeights (microscopicWindow T))
          (normalizedWeights (kineticWindow T)) <=
        (2 / energyFloor) * rawError := by
  intro T hT
  exact (l1Distance_normalizedWeights_le_of_lowerBound
    (microscopicWindow T) (kineticWindow T) hfloor
    (hmicroscopicFloor T hT) (hkineticTotal T hT)
    (hkineticNonneg T hT)).trans
      (mul_le_mul_of_nonneg_left (hraw T hT) (by positivity))

/-! ## The frozen R32 reference profile -/

/-- Positive-mode uniformity transported to the same ordered-mode index type
as `frozenTwoBandEnergy`. -/
def frozenPositiveUniformEnergy
    (N : Nat) [NeZero N] (mode : OrderedModeIndex N) : Real :=
  orderedPositiveUniformWeight N (orderedModeIndexEquivFin N mode)

/-- The frozen two-band energy is already normalized: its total is exactly
one. -/
@[simp] theorem normalizedWeights_frozenTwoBandEnergy
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    normalizedWeights (frozenTwoBandEnergy N) =
      frozenTwoBandEnergy N := by
  funext mode
  unfold normalizedWeights
  rw [show totalWeight (frozenTwoBandEnergy N) = 1 by
    exact sum_frozenTwoBandEnergy_eq_one hN]
  exact div_one _

/-- The frozen quarter-contrast profile is separated from positive-mode
uniformity by at least `1 / 8`, on the ordered-mode index used by the random
mass model. -/
theorem frozenTwoBandEnergy_l1_positiveUniform_lower
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    (1 / 8 : Real) <=
      l1Distance (frozenTwoBandEnergy N)
        (frozenPositiveUniformEnergy N) := by
  have hbase := quarterAmplitude_orderedPositive_l1_lower (N := N) hN
  unfold l1Distance frozenTwoBandEnergy frozenPositiveUniformEnergy
  calc
    (1 / 8 : Real) <=
        ∑ i : Fin N,
          |orderedPositiveInitialEnergyProfile N (1 / 4) i -
            orderedPositiveUniformWeight N i| := hbase
    _ = ∑ mode : OrderedModeIndex N,
          |orderedTargetEnergy N (1 / 4) mode -
            orderedPositiveUniformWeight N
              (orderedModeIndexEquivFin N mode)| := by
      symm
      exact Fintype.sum_equiv (orderedModeIndexEquivFin N)
        (fun mode : OrderedModeIndex N =>
          |orderedTargetEnergy N (1 / 4) mode -
            orderedPositiveUniformWeight N
              (orderedModeIndexEquivFin N mode)|)
        (fun i : Fin N =>
          |orderedPositiveInitialEnergyProfile N (1 / 4) i -
            orderedPositiveUniformWeight N i|)
        (fun _mode => rfl)

/-! ## Uniform frozen-profile consequence -/

/-- Uniform raw closeness to the frozen R32 profile gives uniform normalized
closeness to that same profile.  Only the microscopic late-window total needs
an assumed lower bound; the frozen reference total and nonnegativity are
proved internally. -/
theorem normalized_windowProfile_close_frozen_uniform_in_endpoint
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (microscopicWindow : Real -> OrderedModeIndex N -> Real)
    (endpoints : Set Real) (energyFloor rawError : Real)
    (hfloor : 0 < energyFloor)
    (hmicroscopicFloor : forall T, T ∈ endpoints ->
      energyFloor <= totalWeight (microscopicWindow T))
    (hraw : forall T, T ∈ endpoints ->
      l1Distance (microscopicWindow T) (frozenTwoBandEnergy N) <=
        rawError) :
    forall T, T ∈ endpoints ->
      l1Distance (normalizedWeights (microscopicWindow T))
          (frozenTwoBandEnergy N) <=
        (2 / energyFloor) * rawError := by
  intro T hT
  have hnormalized :=
    l1Distance_normalizedWeights_le_of_lowerBound
      (microscopicWindow T) (frozenTwoBandEnergy N)
      hfloor (hmicroscopicFloor T hT)
      (show 0 < totalWeight (frozenTwoBandEnergy N) by
        rw [show totalWeight (frozenTwoBandEnergy N) = 1 by
          exact sum_frozenTwoBandEnergy_eq_one hN]
        norm_num)
      (frozenTwoBandEnergy_nonneg hN)
  rw [normalizedWeights_frozenTwoBandEnergy hN] at hnormalized
  exact hnormalized.trans
    (mul_le_mul_of_nonneg_left (hraw T hT) (by positivity))

/-- The final R32 bookkeeping statement.  If every raw late-window profile
is within `rawError` of the frozen initial spectrum and retains total energy
at least `energyFloor`, then at every endpoint its normalized distance from
positive-mode equipartition is at least

`1 / 8 - (2 / energyFloor) * rawError`.

Thus an error budget strictly below `energyFloor / 16` preserves a strictly
positive nonequilibrium gap uniformly in the window endpoint. -/
theorem normalized_windowProfile_distance_from_uniform_lower
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (microscopicWindow : Real -> OrderedModeIndex N -> Real)
    (endpoints : Set Real) (energyFloor rawError : Real)
    (hfloor : 0 < energyFloor)
    (hmicroscopicFloor : forall T, T ∈ endpoints ->
      energyFloor <= totalWeight (microscopicWindow T))
    (hraw : forall T, T ∈ endpoints ->
      l1Distance (microscopicWindow T) (frozenTwoBandEnergy N) <=
        rawError) :
    forall T, T ∈ endpoints ->
      (1 / 8 : Real) - (2 / energyFloor) * rawError <=
        l1Distance (normalizedWeights (microscopicWindow T))
          (frozenPositiveUniformEnergy N) := by
  intro T hT
  have hclose := normalized_windowProfile_close_frozen_uniform_in_endpoint
    hN microscopicWindow endpoints energyFloor rawError hfloor
    hmicroscopicFloor hraw T hT
  have htriangle := l1Distance_triangle
    (frozenTwoBandEnergy N)
    (normalizedWeights (microscopicWindow T))
    (frozenPositiveUniformEnergy N)
  have hreverse :
      l1Distance (frozenTwoBandEnergy N)
          (normalizedWeights (microscopicWindow T)) <=
        (2 / energyFloor) * rawError := by
    simpa only [l1Distance, abs_sub_comm] using hclose
  linarith [frozenTwoBandEnergy_l1_positiveUniform_lower hN]

/-- A transparent positive-gap specialization of the preceding estimate. -/
theorem one_sixteenth_le_normalized_windowProfile_distance_from_uniform
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (microscopicWindow : Real -> OrderedModeIndex N -> Real)
    (endpoints : Set Real) (energyFloor rawError : Real)
    (hfloor : 0 < energyFloor)
    (hmicroscopicFloor : forall T, T ∈ endpoints ->
      energyFloor <= totalWeight (microscopicWindow T))
    (hraw : forall T, T ∈ endpoints ->
      l1Distance (microscopicWindow T) (frozenTwoBandEnergy N) <=
        rawError)
    (hbudget : (2 / energyFloor) * rawError <= (1 / 16 : Real)) :
    forall T, T ∈ endpoints ->
      (1 / 16 : Real) <=
        l1Distance (normalizedWeights (microscopicWindow T))
          (frozenPositiveUniformEnergy N) := by
  intro T hT
  have hlower := normalized_windowProfile_distance_from_uniform_lower
    hN microscopicWindow endpoints energyFloor rawError hfloor
    hmicroscopicFloor hraw T hT
  linarith

end

#print axioms normalized_lateWindow_l1Distance_uniform_in_endpoint
#print axioms normalized_windowProfile_l1Distance_uniform_in_endpoint
#print axioms normalizedWeights_frozenTwoBandEnergy
#print axioms frozenTwoBandEnergy_l1_positiveUniform_lower
#print axioms normalized_windowProfile_close_frozen_uniform_in_endpoint
#print axioms normalized_windowProfile_distance_from_uniform_lower
#print axioms one_sixteenth_le_normalized_windowProfile_distance_from_uniform

end ArchonPhysics.R32LateWindowNormalizationStability
