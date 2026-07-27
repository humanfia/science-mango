import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, Problem 3, Part A.2

The source treats the torus as thin and its fields as uniform, so `H`, `B`, and
`M` below are dimension-tagged scalar magnitudes rather than spatial fields.
All `.val` equations are numerical readouts in one coherent system of units.
-/

open Dimension

namespace IPhO2026Problems.Problem3A2

/-- Dimension of an area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- Dimension of a volume. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- Dimension of electric current, expressed using charge and time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Dimension of magnetic field strength `H` and magnetization `M`. -/
def magneticFieldStrengthDimension : Dimension := C𝓭 * T𝓭⁻¹ * L𝓭⁻¹

/-- SI dimension of magnetic flux density `B`. -/
def magneticFluxDensityDimension : Dimension := M𝓭 * C𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of the vacuum permeability `μ₀`. -/
def permeabilityDimension : Dimension := M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Dimension of magnetic flux, and hence of a voltage time-integral. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Dimension of work or heat. -/
def energyDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The geometry labelled in Figure 3a.

`minorRadius` is the source's `r`; the figure labels the corresponding
cross-section diameter as `2r`.  The small dimensionless bound makes the
thin-torus assumption `r ≪ R` explicit.
-/
structure ThinToroidalGeometry where
  meanRadius : WithDim L𝓭 ℝ
  minorRadius : WithDim L𝓭 ℝ
  crossSectionDiameter : WithDim L𝓭 ℝ
  crossSectionArea : WithDim areaDimension ℝ
  volume : WithDim volumeDimension ℝ
  thinnessBound : ℝ
  meanRadius_pos : 0 < meanRadius.val
  minorRadius_pos : 0 < minorRadius.val
  crossSectionArea_pos : 0 < crossSectionArea.val
  volume_pos : 0 < volume.val
  thinnessBound_pos : 0 < thinnessBound
  thinnessBound_lt_one : thinnessBound < 1
  minorRadius_le_thinness : minorRadius.val ≤ thinnessBound * meanRadius.val
  diameter_eq_two_minorRadii :
    crossSectionDiameter.val = 2 * minorRadius.val
  circularCrossSection :
    crossSectionArea.val = Real.pi * minorRadius.val ^ 2
  torusVolume :
    volume.val = (2 * Real.pi * meanRadius.val) * crossSectionArea.val

/-- The insulated, densely wound, negligible-resistance wire of Figure 3a.

The orientation records which toroidal sense is positive for current and flux.
-/
inductive ToroidalOrientation
  | clockwise
  | counterclockwise
  deriving DecidableEq

structure IdealToroidalWinding where
  turns : ℕ
  current : WithDim electricCurrentDimension ℝ
  positiveOrientation : ToroidalOrientation
  turns_pos : 0 < turns
  current_nonneg : 0 ≤ current.val

/-- Uniform scalar magnetic state of the homogeneous isotropic paramagnet.

The scalar susceptibility equation records that `M` is parallel to `H`.
`ampereCircuitLaw` is Ampère's law around the mean toroidal loop.  The final
field records the reusable result of Part A.1 without importing its Lean file.
-/
structure UniformParamagneticState
    (geometry : ThinToroidalGeometry) (winding : IdealToroidalWinding) where
  fieldStrength : WithDim magneticFieldStrengthDimension ℝ
  fluxDensity : WithDim magneticFluxDensityDimension ℝ
  magnetization : WithDim magneticFieldStrengthDimension ℝ
  vacuumPermeability : WithDim permeabilityDimension ℝ
  susceptibility : ℝ
  fieldStrength_nonneg : 0 ≤ fieldStrength.val
  fluxDensity_nonneg : 0 ≤ fluxDensity.val
  magnetization_nonneg : 0 ≤ magnetization.val
  vacuumPermeability_pos : 0 < vacuumPermeability.val
  susceptibility_pos : 0 < susceptibility
  homogeneousIsotropicParamagneticLaw :
    magnetization.val = susceptibility * fieldStrength.val
  magneticConstitutiveLaw :
    fluxDensity.val =
      vacuumPermeability.val * (fieldStrength.val + magnetization.val)
  ampereCircuitLaw :
    fieldStrength.val * (2 * Real.pi * geometry.meanRadius.val) =
      (winding.turns : ℝ) * winding.current.val
  previousPartFieldMagnitude :
    fieldStrength.val =
      (winding.turns : ℝ) * winding.current.val *
        geometry.crossSectionArea.val / geometry.volume.val

/-- Direction of an energy transfer relative to the paramagnetic torus. -/
inductive EnergyTransferDirection
  | intoTorus
  | outOfTorus
  deriving DecidableEq

/-- The problem's sign convention: energy entering is nonnegative and energy
leaving is nonpositive.  This applies to both work and heat. -/
def SignConsistentEnergyTransfer
    (direction : EnergyTransferDirection)
    (amount : WithDim energyDimension ℝ) : Prop :=
  match direction with
  | .intoTorus => 0 ≤ amount.val
  | .outOfTorus => amount.val ≤ 0

/-- A signed work or heat transfer with its physical direction exposed. -/
structure SignedEnergyTransfer where
  amount : WithDim energyDimension ℝ
  direction : EnergyTransferDirection
  sign_consistent : SignConsistentEnergyTransfer direction amount

/-- Infinitesimal change used in Part A.2.

The three governing equations separate the dense-winding flux law, Faraday's
law with the external-source polarity, and the electrical work law.  Thus the
requested closed form is not assumed.  The zero wire-heating equation records
the negligible-resistance approximation from the apparatus description.
-/
structure InfinitesimalMagneticChange
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (_state : UniformParamagneticState geometry winding) where
  fluxDensityChange : WithDim magneticFluxDensityDimension ℝ
  fluxChangePerTurn : WithDim magneticFluxDimension ℝ
  fluxLinkageChange : WithDim magneticFluxDimension ℝ
  externalVoltageTimeIntegral : WithDim magneticFluxDimension ℝ
  sourceWork : SignedEnergyTransfer
  torusHeat : SignedEnergyTransfer
  wireJouleHeat : WithDim energyDimension ℝ
  positiveFluxOrientation : ToroidalOrientation
  orientation_agrees_with_winding :
    positiveFluxOrientation = winding.positiveOrientation
  fluxPerTurnLaw :
    fluxChangePerTurn.val =
      geometry.crossSectionArea.val * fluxDensityChange.val
  denseWindingFluxLinkageLaw :
    fluxLinkageChange.val =
      (winding.turns : ℝ) * fluxChangePerTurn.val
  externalSourceFaradayLaw :
    externalVoltageTimeIntegral.val = fluxLinkageChange.val
  sourcePowerWorkLaw :
    sourceWork.amount.val =
      winding.current.val * externalVoltageTimeIntegral.val
  negligibleWireHeating :
    wireJouleHeat.val = 0

/-- Faraday's law and the electrical work law give the intermediate expression
`dW_emf = I N A dB`, before using the result of Part A.1. -/
lemma source_work_eq_current_turns_area_dB
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (state : UniformParamagneticState geometry winding)
    (change : InfinitesimalMagneticChange geometry winding state) :
    change.sourceWork.amount.val =
      winding.current.val * (winding.turns : ℝ) *
        geometry.crossSectionArea.val * change.fluxDensityChange.val := by
  rw [change.sourcePowerWorkLaw, change.externalSourceFaradayLaw,
    change.denseWindingFluxLinkageLaw, change.fluxPerTurnLaw]
  ring

/-- **IPhO 2026 Problem 3 A.2.**

For the positive-entering energy convention, the infinitesimal work performed
by the external voltage source is `dW_emf = V H dB`.
-/
theorem external_source_work_for_flux_density_change
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (state : UniformParamagneticState geometry winding)
    (change : InfinitesimalMagneticChange geometry winding state) :
    change.sourceWork.amount.val =
      geometry.volume.val * state.fieldStrength.val *
        change.fluxDensityChange.val := by
  calc
    change.sourceWork.amount.val =
        winding.current.val * (winding.turns : ℝ) *
          geometry.crossSectionArea.val * change.fluxDensityChange.val :=
      source_work_eq_current_turns_area_dB geometry winding state change
    _ = geometry.volume.val * state.fieldStrength.val *
        change.fluxDensityChange.val := by
      rw [state.previousPartFieldMagnitude]
      field_simp [ne_of_gt geometry.volume_pos]

end IPhO2026Problems.Problem3A2
