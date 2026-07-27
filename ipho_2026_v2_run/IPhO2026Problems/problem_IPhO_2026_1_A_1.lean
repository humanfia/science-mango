import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, theoretical problem 1, part A.1

This file models the hydrostatic gate in Figure 1a. Physical scalars are
represented by Physlib's dimension-tagged `WithDim` type. Their `val` fields
are the numerical readouts in one fixed coherent SI unit system.
-/

namespace IPhO2026Problems
namespace HydrostaticGateA1

open Dimension

/-- Dimension of an area. -/
def areaDimension : Dimension := L𝓭 ^ (2 : ℕ)

/-- Dimension of a volume. -/
def volumeDimension : Dimension := L𝓭 ^ (3 : ℕ)

/-- Dimension of mass density. -/
def massDensityDimension : Dimension := M𝓭 / L𝓭 ^ (3 : ℕ)

/-- Dimension of acceleration. -/
def accelerationDimension : Dimension := L𝓭 / T𝓭 ^ (2 : ℕ)

/-- Dimension of force. -/
def forceDimension : Dimension := M𝓭 * L𝓭 / T𝓭 ^ (2 : ℕ)

/-- Dimension of pressure. -/
def pressureDimension : Dimension := M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of torque. -/
def torqueDimension : Dimension := forceDimension * L𝓭

/-- The three labelled points appearing in Figure 1a. -/
inductive FigurePoint where
  | M
  | N
  | O
  deriving DecidableEq, Repr

/-- The vertical wall in Figure 1a has labelled endpoints `M` and `N`. -/
def wallMN : FigurePoint × FigurePoint := (.M, .N)

/-- The frictionless rotation axis passes through the labelled point `O`. -/
def hingePoint : FigurePoint := .O

/-- Orientation data needed to distinguish the two opposing torques. -/
inductive TorqueSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Dimensioned geometric readouts from the cube, slot, and lever arms in Figure 1a. -/
structure Figure1aGeometry where
  sideLength : WithDim L𝓭 ℝ
  cubeVolume : WithDim volumeDimension ℝ
  slotWidth : WithDim L𝓭 ℝ
  slotVerticalSize : WithDim L𝓭 ℝ
  openingArea : WithDim areaDimension ℝ
  pressureLeverArm : WithDim L𝓭 ℝ
  effectiveWeightLeverArm : WithDim L𝓭 ℝ
  lowerContactLeverArm : WithDim L𝓭 ℝ

/--
The mathematical consequences of the geometry in Figure 1a.

In particular, the slot has width `a`, vertical size `a * √2 / 2`, and the
pressure and effective-weight lever arms about `O` are both `a / (2 * √2)`.
-/
structure MatchesFigure1a (geometry : Figure1aGeometry) : Prop where
  sideLength_pos : 0 < geometry.sideLength.val
  cubeVolume_eq :
    geometry.cubeVolume.val = geometry.sideLength.val ^ 3
  slotWidth_eq :
    geometry.slotWidth.val = geometry.sideLength.val
  slotVerticalSize_eq :
    geometry.slotVerticalSize.val =
      geometry.sideLength.val * Real.sqrt 2 / 2
  openingArea_eq :
    geometry.openingArea.val =
      geometry.slotWidth.val * geometry.slotVerticalSize.val
  pressureLeverArm_eq :
    geometry.pressureLeverArm.val =
      geometry.sideLength.val / (2 * Real.sqrt 2)
  effectiveWeightLeverArm_eq :
    geometry.effectiveWeightLeverArm.val =
      geometry.sideLength.val / (2 * Real.sqrt 2)
  lowerContactLeverArm_nonneg :
    0 ≤ geometry.lowerContactLeverArm.val

/--
All physical quantities needed for the two reservoirs, the submerged cube,
and the forces and torques acting on it.
-/
structure HydrostaticGate where
  geometry : Figure1aGeometry
  leftWaterLevel : WithDim L𝓭 ℝ
  rightWaterLevel : WithDim L𝓭 ℝ
  levelDifference : WithDim L𝓭 ℝ
  waterDensity : WithDim massDensityDimension ℝ
  blockDensity : WithDim massDensityDimension ℝ
  gravitationalAcceleration : WithDim accelerationDimension ℝ
  submergedVolume : WithDim volumeDimension ℝ
  pressureDifference : WithDim pressureDimension ℝ
  pressureForceDifference : WithDim forceDimension ℝ
  weightForce : WithDim forceDimension ℝ
  buoyancyForce : WithDim forceDimension ℝ
  effectiveWeightForce : WithDim forceDimension ℝ
  hingeReactionForce : WithDim forceDimension (Fin 2 → ℝ)
  lowerEdgeContactForce : WithDim forceDimension ℝ
  pressureTorque : WithDim torqueDimension ℝ
  effectiveWeightTorque : WithDim torqueDimension ℝ
  hingeTorque : WithDim torqueDimension ℝ
  lowerEdgeContactTorque : WithDim torqueDimension ℝ
  pressureTorqueSense : TorqueSense
  effectiveWeightTorqueSense : TorqueSense

/--
Hydrostatic, buoyancy, weight, and moment-arm laws for the fully submerged
cube. These equations are independent of the requested value of `a`.
-/
structure ObeysHydrostaticLaws (gate : HydrostaticGate) : Prop where
  leftLevel_higher :
    gate.rightWaterLevel.val < gate.leftWaterLevel.val
  levelDifference_eq :
    gate.levelDifference.val =
      gate.leftWaterLevel.val - gate.rightWaterLevel.val
  waterDensity_pos :
    0 < gate.waterDensity.val
  blockDensity_gt_water :
    gate.waterDensity.val < gate.blockDensity.val
  gravitationalAcceleration_pos :
    0 < gate.gravitationalAcceleration.val
  fullSubmersion :
    gate.submergedVolume.val = gate.geometry.cubeVolume.val
  pressureDifference_eq :
    gate.pressureDifference.val =
      gate.waterDensity.val * gate.gravitationalAcceleration.val *
        gate.levelDifference.val
  pressureForce_eq :
    gate.pressureForceDifference.val =
      gate.pressureDifference.val * gate.geometry.openingArea.val
  weightForce_eq :
    gate.weightForce.val =
      gate.blockDensity.val * gate.gravitationalAcceleration.val *
        gate.geometry.cubeVolume.val
  buoyancyForce_eq :
    gate.buoyancyForce.val =
      gate.waterDensity.val * gate.gravitationalAcceleration.val *
        gate.submergedVolume.val
  effectiveWeightForce_eq :
    gate.effectiveWeightForce.val =
      gate.weightForce.val - gate.buoyancyForce.val
  pressureTorque_eq :
    gate.pressureTorque.val =
      gate.pressureForceDifference.val * gate.geometry.pressureLeverArm.val
  effectiveWeightTorque_eq :
    gate.effectiveWeightTorque.val =
      gate.effectiveWeightForce.val *
        gate.geometry.effectiveWeightLeverArm.val
  lowerEdgeContactTorque_eq :
    gate.lowerEdgeContactTorque.val =
      gate.lowerEdgeContactForce.val * gate.geometry.lowerContactLeverArm.val

/--
The limiting configuration described in the official solution: the lower
edge of the opening has just lost contact with the cube, the hinge contributes
no torque about `O`, and the two oppositely oriented torque magnitudes balance.
-/
structure AtMaximumPermissibleDifference (gate : HydrostaticGate) : Prop where
  pressure_torque_orientation :
    gate.pressureTorqueSense = .counterclockwise
  effective_weight_torque_orientation :
    gate.effectiveWeightTorqueSense = .clockwise
  lowerEdgeContactForce_zero :
    gate.lowerEdgeContactForce.val = 0
  hingeTorque_zero :
    gate.hingeTorque.val = 0
  torqueBalance :
    gate.pressureTorque.val + gate.hingeTorque.val =
      gate.effectiveWeightTorque.val + gate.lowerEdgeContactTorque.val

/-- The numerical data printed in the problem statement. -/
structure MatchesProblemData (gate : HydrostaticGate) : Prop where
  blockDensity_eq :
    gate.blockDensity.val = 3 * gate.waterDensity.val
  maximumLevelDifference_eq :
    gate.levelDifference.val = 1.41

/--
Figure 1a's slot geometry gives the effective opening area
`a² / √2`.
-/
lemma opening_area_readout
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry) :
    gate.geometry.openingArea.val =
      gate.geometry.sideLength.val ^ 2 / Real.sqrt 2 := by
  rw [hFigure.openingArea_eq, hFigure.slotWidth_eq,
    hFigure.slotVerticalSize_eq]
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

/--
At the limiting configuration, the zero contact and hinge torques reduce
static equilibrium to equality of the pressure and effective-weight torques.
-/
lemma critical_torque_balance
    (gate : HydrostaticGate)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate) :
    gate.pressureTorque.val = gate.effectiveWeightTorque.val := by
  have hLowerTorque : gate.lowerEdgeContactTorque.val = 0 := by
    rw [hLaws.lowerEdgeContactTorque_eq,
      hCritical.lowerEdgeContactForce_zero, zero_mul]
  linarith [hCritical.torqueBalance, hCritical.hingeTorque_zero, hLowerTorque]

/--
The hydrostatic and torque equations determine the cube side in terms of
the two densities and the level difference.
-/
lemma side_length_from_hydrostatic_balance
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate) :
    gate.geometry.sideLength.val =
      gate.waterDensity.val * gate.levelDifference.val /
        (Real.sqrt 2 * (gate.blockDensity.val - gate.waterDensity.val)) := by
  have hBalance := critical_torque_balance gate hLaws hCritical
  rw [hLaws.pressureTorque_eq, hLaws.pressureForce_eq,
    hLaws.pressureDifference_eq, opening_area_readout gate hFigure,
    hFigure.pressureLeverArm_eq, hLaws.effectiveWeightTorque_eq,
    hLaws.effectiveWeightForce_eq, hLaws.weightForce_eq,
    hFigure.cubeVolume_eq, hLaws.buoyancyForce_eq,
    hLaws.fullSubmersion, hFigure.cubeVolume_eq,
    hFigure.effectiveWeightLeverArm_eq] at hBalance
  field_simp at hBalance
  have hFactor :
      0 < gate.gravitationalAcceleration.val *
        gate.geometry.sideLength.val ^ 3 :=
    mul_pos hLaws.gravitationalAcceleration_pos
      (pow_pos hFigure.sideLength_pos 3)
  have hDensityDiff :
      0 < gate.blockDensity.val - gate.waterDensity.val :=
    sub_pos.mpr hLaws.blockDensity_gt_water
  field_simp
  nlinarith

/--
For a block of density `3ρ₀`, the general critical-balance formula simplifies
to `a = Δh / (2√2)`.
-/
lemma side_length_for_triple_density
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate)
    (hDensity : gate.blockDensity.val = 3 * gate.waterDensity.val) :
    gate.geometry.sideLength.val =
      gate.levelDifference.val / (2 * Real.sqrt 2) := by
  rw [side_length_from_hydrostatic_balance gate hFigure hLaws hCritical,
    hDensity]
  have hrho : gate.waterDensity.val ≠ 0 :=
    ne_of_gt hLaws.waterDensity_pos
  field_simp
  ring

/--
The exact value obtained from `Δh = 1.41 m` is within half of one hundredth
of `0.50 m`, so `0.50 m` is the correct two-decimal report.
-/
lemma stated_value_rounds_to_half_meter :
    |(1.41 : ℝ) / (2 * Real.sqrt 2) - 0.50| < 0.005 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hLowerSqrt : (141 : ℝ) / 101 < Real.sqrt 2 := by
    nlinarith [hsqrt_sq]
  have hUpperSqrt : Real.sqrt 2 < (47 : ℝ) / 33 := by
    nlinarith [hsqrt_sq]
  rw [abs_lt]
  constructor <;> field_simp <;> nlinarith

end HydrostaticGateA1

open HydrostaticGateA1

/--
IPhO 2026 T1-A1: the critical cube side is `Δh / (2√2)`. For the stated
`Δh = 1.41 m`, its exact SI readout rounds to the reported `0.50 m` at two
decimal places; the strict `0.005 m` error bound expresses that rounding and
is not an experimental-uncertainty assumption.
-/
theorem problem_IPhO_2026_1_A_1
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate)
    (hData : MatchesProblemData gate) :
    gate.geometry.sideLength.val =
        gate.levelDifference.val / (2 * Real.sqrt 2) ∧
      |gate.geometry.sideLength.val - 0.50| < 0.005 := by
  constructor
  · exact side_length_for_triple_density gate hFigure hLaws hCritical
      hData.blockDensity_eq
  · rw [side_length_for_triple_density gate hFigure hLaws hCritical
        hData.blockDensity_eq, hData.maximumLevelDifference_eq]
    exact stated_value_rounds_to_half_meter

end IPhO2026Problems
