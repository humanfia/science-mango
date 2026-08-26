import ArchonPhysics.QuantitativeThermodynamicRelaxation
import ArchonPhysics.ThermodynamicEquipartitionLimit

/-!
# Exponential relaxation as thermodynamic tail control

This module packages a uniform exponential relaxation estimate with a
finite-size remainder into the transparent `ThermodynamicTailControl`
interface.  The resulting settling bound is the explicit logarithmic bound
from `QuantitativeThermodynamicRelaxation`.
-/

namespace ArchonPhysics.ThermodynamicEquipartitionRelaxation

open Filter Topology
open ArchonPhysics.QuantitativeThermodynamicRelaxation
open ArchonPhysics.ThermodynamicEquipartitionLimit

noncomputable section

/-- A nonnegative finite-size remainder strictly below a vanishing tolerance
also vanishes in the thermodynamic limit. -/
theorem remainder_tendsto_zero_of_nonneg_lt_tolerance
    {remainder tolerance : Nat -> Real}
    (hremainderNonneg : forall N, 0 <= remainder N)
    (hremainder : forall N, remainder N < tolerance N)
    (htoleranceZero : Tendsto tolerance atTop (nhds 0)) :
    Tendsto remainder atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall hremainderNonneg
  · exact Filter.Eventually.of_forall fun N => (hremainder N).le
  · exact htoleranceZero

/-- A uniform exponential relaxation estimate, with a vanishing nonnegative
tolerance, supplies thermodynamic tail control.  Its settling bound is exactly
the logarithmic bound for the finite-size remainder at each size. -/
def exponentialThermodynamicTailControl
    (Delta : Nat -> Real -> Real)
    (remainder tolerance : Nat -> Real)
    (C kappa g : Real)
    (hC : 0 < C) (hkappa : 0 < kappa) (hg : g ≠ 0)
    (hremainderNonneg : forall N, 0 <= remainder N)
    (hremainder : forall N, remainder N < tolerance N)
    (htolerance : forall N, tolerance N - remainder N <= C)
    (htoleranceNonneg : forall N, 0 <= tolerance N)
    (htoleranceZero : Tendsto tolerance atTop (nhds 0))
    (hDeltaNonneg : forall N t, 0 <= Delta N t)
    (htail : forall N t, 0 <= t ->
      Delta N t <=
        C * Real.exp (-(kappa * g ^ 2 * t)) + remainder N) :
    ThermodynamicTailControl Delta where
  tolerance := tolerance
  settlingBound := fun N =>
    exponentialSettlingBound C kappa g (remainder N) (tolerance N)
  tolerance_nonneg := htoleranceNonneg
  tolerance_tendsto_zero :=
    (show IsVanishingToleranceSchedule remainder tolerance from
      ⟨remainder_tendsto_zero_of_nonneg_lt_tolerance
          hremainderNonneg hremainder htoleranceZero,
        htoleranceZero, Filter.Eventually.of_forall hremainder⟩).tolerance_tendsto
  settlingBound_nonneg := fun N =>
    exponentialSettlingBound_nonnegative
      hkappa hg (hremainder N) (htolerance N)
  error_tail := by
    intro N t hsettled
    refine ⟨hDeltaNonneg N t, ?_⟩
    exact error_le_of_exponential_tail_of_settlingBound_le
      (Delta N) hC hkappa hg (hremainder N) (htolerance N)
        (htail N) hsettled

/-- Along any growing-size path observed after the explicit size-dependent
settling bound, the nonnegative equipartition error tends to zero. -/
theorem error_tendsto_zero_along_growing_size
    (Delta : Nat -> Real -> Real)
    (remainder tolerance : Nat -> Real)
    (C kappa g : Real)
    (hC : 0 < C) (hkappa : 0 < kappa) (hg : g ≠ 0)
    (hremainderNonneg : forall N, 0 <= remainder N)
    (hremainder : forall N, remainder N < tolerance N)
    (htolerance : forall N, tolerance N - remainder N <= C)
    (htoleranceNonneg : forall N, 0 <= tolerance N)
    (htoleranceZero : Tendsto tolerance atTop (nhds 0))
    (hDeltaNonneg : forall N t, 0 <= Delta N t)
    (htail : forall N t, 0 <= t ->
      Delta N t <=
        C * Real.exp (-(kappa * g ^ 2 * t)) + remainder N)
    (side : Nat -> Nat) (observationTime : Nat -> Real)
    (hside : Tendsto side atTop atTop)
    (hobservation : forall j,
      exponentialSettlingBound C kappa g
          (remainder (side j)) (tolerance (side j)) <=
        observationTime j) :
    Tendsto
      (fun j => Delta (side j) (observationTime j))
      atTop (nhds 0) := by
  let control : ThermodynamicTailControl Delta :=
    exponentialThermodynamicTailControl Delta remainder tolerance C kappa g
      hC hkappa hg hremainderNonneg hremainder htolerance htoleranceNonneg
        htoleranceZero hDeltaNonneg htail
  apply control.error_tendsto_zero_along side observationTime hside
  intro j
  exact hobservation j

end

end ArchonPhysics.ThermodynamicEquipartitionRelaxation
