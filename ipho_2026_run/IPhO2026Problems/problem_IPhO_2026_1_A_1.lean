import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 1, part A.1: hydrostatic gate

The quantities below are SI readouts wrapped in Physlib's `WithDim`, so their
physical dimensions are part of their Lean types.  The figure data and
governing hydrostatic laws are hypotheses; the requested value of the cube side
is only a conclusion of `sideLength_at_maximumLevelDifference`.
-/

namespace IPhO2026Problems.IPhO2026_1_A_1

open Dimension

/-- A length read in metres. -/
abbrev LengthSI := WithDim L𝓭 ℝ

/-- An area read in square metres. -/
abbrev AreaSI := WithDim (L𝓭 * L𝓭) ℝ

/-- A volume read in cubic metres. -/
abbrev VolumeSI := WithDim (L𝓭 * L𝓭 * L𝓭) ℝ

/-- A mass density read in kilograms per cubic metre. -/
abbrev MassDensitySI := WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ

/-- An acceleration read in metres per second squared. -/
abbrev AccelerationSI := WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- A pressure read in pascals. -/
abbrev PressureSI := WithDim (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- A force read in newtons. -/
abbrev ForceSI := WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- A torque read in newton metres. -/
abbrev TorqueSI := WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ

/-- Point labels appearing in Figure 1a. -/
inductive FigurePointLabel
  | M
  | N
  | O
  deriving DecidableEq

/-- Orientations relevant to the wall in Figure 1a. -/
inductive WallOrientation
  | vertical
  | other
  deriving DecidableEq

/-- The possible submersion status of the sealing block. -/
inductive SubmersionStatus
  | fullySubmerged
  | notFullySubmerged
  deriving DecidableEq

/-- The hinge property relevant to the onset of rotation. -/
inductive HingeFriction
  | frictionless
  | frictional
  deriving DecidableEq

/-- The orientation of the hinge axis relative to the plane of Figure 1a. -/
inductive AxisOrientation
  | perpendicularToFigure
  | other
  deriving DecidableEq

/-- The material in the two reservoirs. -/
inductive ReservoirFluid
  | water
  | other
  deriving DecidableEq

/-- Qualitative apparatus data stated in the problem and shown in Figure 1a. -/
structure GateConfiguration where
  wallTopLabel : FigurePointLabel
  wallBottomLabel : FigurePointLabel
  hingeLabel : FigurePointLabel
  wallOrientation : WallOrientation
  submersion : SubmersionStatus
  hingeFriction : HingeFriction
  rotationAxis : AxisOrientation
  reservoirFluid : ReservoirFluid
  leftReservoirCanReceiveWater : Bool

/--
The dimensional geometric readouts from Figure 1a.  In particular, the slot
has depth `a` into the plane of the drawing and vertical size `a * √2 / 2`.
-/
structure Figure1aGeometry where
  cubeSideSI : LengthSI
  slotVerticalSizeSI : LengthSI
  hingeToSlotEdgeSI : LengthSI
  slotAreaSI : AreaSI
  cubeVolumeSI : VolumeSI
  pressureLeverArmAboutO_SI : LengthSI
  effectiveWeightLeverArmAboutO_SI : LengthSI

/-- Dimensional state variables used in the limiting moment balance. -/
structure HydrostaticGateState where
  waterDensitySI : MassDensitySI
  cubeDensitySI : MassDensitySI
  gravitationalAccelerationSI : AccelerationSI
  maximumLevelDifferenceSI : LengthSI
  pressureDifferenceSI : PressureSI
  pressureResultantSI : ForceSI
  effectiveWeightSI : ForceSI
  pressureTorqueAboutO_SI : TorqueSI
  effectiveWeightTorqueAboutO_SI : TorqueSI

/--
The qualitative conditions and numerical data supplied by the problem.
The density ratio and `1.41 m` level difference are data readouts, not the
answer requested in part A.1.
-/
structure MatchesProblemSetup
    (configuration : GateConfiguration)
    (geometry : Figure1aGeometry)
    (state : HydrostaticGateState) : Prop where
  wallLabels :
    configuration.wallTopLabel = .M ∧
      configuration.wallBottomLabel = .N ∧
      configuration.hingeLabel = .O
  wallVertical : configuration.wallOrientation = .vertical
  cubeFullySubmerged : configuration.submersion = .fullySubmerged
  hingeFrictionless : configuration.hingeFriction = .frictionless
  axisPerpendicular : configuration.rotationAxis = .perpendicularToFigure
  reservoirsContainWater : configuration.reservoirFluid = .water
  leftReservoirHasSource : configuration.leftReservoirCanReceiveWater = true
  cubeSide_pos : 0 < geometry.cubeSideSI.val
  waterDensity_pos : 0 < state.waterDensitySI.val
  gravitationalAcceleration_pos : 0 < state.gravitationalAccelerationSI.val
  cubeDensityRatio :
    state.cubeDensitySI.val = 3 * state.waterDensitySI.val
  statedMaximumLevelDifference :
    state.maximumLevelDifferenceSI.val = 141 / 100

/--
Metric relations read from Figure 1a.  The pressure resultant acts through the
centre of the rectangular slot, and the effective weight acts through the
centre of the cube.
-/
structure MatchesFigure1a
    (geometry : Figure1aGeometry) : Prop where
  slotVerticalSize :
    geometry.slotVerticalSizeSI.val =
      geometry.cubeSideSI.val * Real.sqrt 2 / 2
  hingeToSlotEdge :
    geometry.hingeToSlotEdgeSI.val = geometry.cubeSideSI.val / 2
  slotArea :
    geometry.slotAreaSI.val =
      geometry.cubeSideSI.val * geometry.slotVerticalSizeSI.val
  cubeVolume :
    geometry.cubeVolumeSI.val = geometry.cubeSideSI.val ^ 3
  pressureLeverArm :
    geometry.pressureLeverArmAboutO_SI.val =
      geometry.slotVerticalSizeSI.val / 2
  effectiveWeightLeverArm :
    geometry.effectiveWeightLeverArmAboutO_SI.val =
      geometry.cubeSideSI.val / (2 * Real.sqrt 2)

/--
The governing physical laws at the maximum permissible level difference:
hydrostatic pressure, resultant force, buoyancy-reduced weight, the two moments
about the frictionless hinge `O`, and equality of those moments at incipient
rotation.
-/
structure HydrostaticGateLaws
    (geometry : Figure1aGeometry)
    (state : HydrostaticGateState) : Prop where
  hydrostaticPressureDifference :
    state.pressureDifferenceSI.val =
      state.waterDensitySI.val *
        state.gravitationalAccelerationSI.val *
        state.maximumLevelDifferenceSI.val
  pressureResultant :
    state.pressureResultantSI.val =
      state.pressureDifferenceSI.val * geometry.slotAreaSI.val
  effectiveWeight :
    state.effectiveWeightSI.val =
      (state.cubeDensitySI.val - state.waterDensitySI.val) *
        state.gravitationalAccelerationSI.val *
        geometry.cubeVolumeSI.val
  pressureMomentAboutO :
    state.pressureTorqueAboutO_SI.val =
      state.pressureResultantSI.val *
        geometry.pressureLeverArmAboutO_SI.val
  effectiveWeightMomentAboutO :
    state.effectiveWeightTorqueAboutO_SI.val =
      state.effectiveWeightSI.val *
        geometry.effectiveWeightLeverArmAboutO_SI.val
  limitingMomentBalance :
    state.pressureTorqueAboutO_SI.val =
      state.effectiveWeightTorqueAboutO_SI.val

/--
`length` rounds to `centimetreCount` centimetres when its SI readout lies
within half a centimetre of that decimal value.
-/
def RoundsToNearestCentimeterSI
    (length : LengthSI) (centimetreCount : ℤ) : Prop :=
  |length.val - (centimetreCount : ℝ) / 100| ≤ 1 / 200

/--
At the limiting water-level difference, the cube side is
`Δh / (2 * √2)` and hence rounds to `0.50 m`.

Blueprint label: `thm:physics:IPhO_2026_1_A_1:target`.
-/
theorem sideLength_at_maximumLevelDifference
    (configuration : GateConfiguration)
    (geometry : Figure1aGeometry)
    (state : HydrostaticGateState)
    (hSetup : MatchesProblemSetup configuration geometry state)
    (hFigure : MatchesFigure1a geometry)
    (hLaws : HydrostaticGateLaws geometry state) :
    geometry.cubeSideSI =
        ⟨state.maximumLevelDifferenceSI.val / (2 * Real.sqrt 2)⟩ ∧
      RoundsToNearestCentimeterSI geometry.cubeSideSI 50 := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  have hsqrt2_cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 3 = Real.sqrt 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt2_sq]; ring
  have hbalance := hLaws.limitingMomentBalance
  rw [hLaws.pressureMomentAboutO, hLaws.effectiveWeightMomentAboutO,
    hLaws.pressureResultant, hLaws.effectiveWeight,
    hLaws.hydrostaticPressureDifference, hFigure.slotArea,
    hFigure.cubeVolume, hFigure.pressureLeverArm,
    hFigure.effectiveWeightLeverArm, hFigure.slotVerticalSize,
    hSetup.cubeDensityRatio] at hbalance
  have hfactor :
      state.waterDensitySI.val * state.gravitationalAccelerationSI.val *
          geometry.cubeSideSI.val ^ 3 *
          (state.maximumLevelDifferenceSI.val * Real.sqrt 2 -
            4 * geometry.cubeSideSI.val) = 0 := by
    field_simp [hsqrt2_ne] at hbalance
    rw [hsqrt2_cube] at hbalance
    linear_combination (1 / 2) * hbalance
  have hphysical_ne :
      state.waterDensitySI.val * state.gravitationalAccelerationSI.val *
          geometry.cubeSideSI.val ^ 3 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt hSetup.waterDensity_pos)
        (ne_of_gt hSetup.gravitationalAcceleration_pos))
      (pow_ne_zero 3 (ne_of_gt hSetup.cubeSide_pos))
  have hremaining :
      state.maximumLevelDifferenceSI.val * Real.sqrt 2 -
          4 * geometry.cubeSideSI.val = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hphysical_ne
  have hside :
      geometry.cubeSideSI.val =
        state.maximumLevelDifferenceSI.val / (2 * Real.sqrt 2) := by
    have hsqrt2_recip :
        Real.sqrt 2 / 4 = 1 / (2 * Real.sqrt 2) := by
      field_simp [hsqrt2_ne]
      nlinarith [hsqrt2_sq]
    calc
      geometry.cubeSideSI.val =
          state.maximumLevelDifferenceSI.val * Real.sqrt 2 / 4 := by
        nlinarith [hremaining]
      _ = state.maximumLevelDifferenceSI.val * (Real.sqrt 2 / 4) := by ring
      _ = state.maximumLevelDifferenceSI.val * (1 / (2 * Real.sqrt 2)) := by
        rw [hsqrt2_recip]
      _ = state.maximumLevelDifferenceSI.val / (2 * Real.sqrt 2) := by ring
  have hlength :
      geometry.cubeSideSI =
        ⟨state.maximumLevelDifferenceSI.val / (2 * Real.sqrt 2)⟩ := by
    apply WithDim.ext
    exact hside
  refine ⟨hlength, ?_⟩
  unfold RoundsToNearestCentimeterSI
  rw [hside, hSetup.statedMaximumLevelDifference]
  have hsqrt2_lower : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), hsqrt2_sq]
  have hsqrt2_upper : Real.sqrt 2 ≤ (99 / 70 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), hsqrt2_sq]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : 0 < (2 : ℝ) * Real.sqrt 2)]
    norm_num at hsqrt2_upper ⊢
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : 0 < (2 : ℝ) * Real.sqrt 2)]
    norm_num at hsqrt2_lower ⊢
    nlinarith

end IPhO2026Problems.IPhO2026_1_A_1
