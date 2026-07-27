import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

/-!
# IPhO 2026, problem 1, part C.2

The dimensional quantities below use Physlib's `Dimensionful`/`WithDim`
infrastructure.  Scalar real numbers are used only for explicit SI, electronvolt,
atomic-mass-unit, angle, or figure-coordinate readouts.
-/

noncomputable section

open Dimension
open UnitChoices
open CarriesDimension

namespace IPhO2026_1_C_2

/-- A physical mass, represented independently of a choice of units. -/
abbrev DimMass : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- An angular frequency, with physical dimension inverse time. -/
abbrev DimAngularFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- An action, the dimension carried by the reduced Planck constant. -/
abbrev DimAction : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹) ℝ)

/-- A dimensionful spatial momentum. -/
abbrev DimMomentum (d : ℕ := 3) : Type := Dimensionful (Momentum d)

/-- The atomic mass unit, using its SI value in kilograms. -/
def atomicMassUnit : DimMass :=
  toDimensionful SI ⟨1.66053906660e-27⟩

/-- SI energy readout, in joules. -/
def energySI (energy : DimEnergy) : ℝ := (energy SI).val

/-- SI mass readout, in kilograms. -/
def massSI (mass : DimMass) : ℝ := (mass SI).val

/-- SI angular-frequency readout, in radians per second. -/
def angularFrequencySI (frequency : DimAngularFrequency) : ℝ :=
  (frequency SI).val

/-- SI action readout, in joule-seconds. -/
def actionSI (action : DimAction) : ℝ := (action SI).val

/-- SI coordinate readout of a dimensionful momentum. -/
def momentumSI {d : ℕ} (momentum : DimMomentum d) : Fin d → ℝ :=
  (momentum SI).val

/-- The number of electronvolts in a physical energy. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energySI energy / energySI DimEnergy.electronVolt

/-- The number of atomic mass units in a physical mass. -/
def massInAtomicMassUnits (mass : DimMass) : ℝ :=
  massSI mass / massSI atomicMassUnit

/-- The rest energy `m c²`, expressed in electronvolts. -/
def restEnergyInElectronVolts (mass : DimMass) : ℝ :=
  massSI mass * (DimSpeed.speedOfLight SI).val ^ 2 /
    energySI DimEnergy.electronVolt

/-- The source diagram used to specify the momentum geometry. -/
inductive SourceFigure where
  | fig1c
  deriving DecidableEq

/--
Physical data for the threshold photodissociation
`γ + O₃ → O₂ + O` shown in Fig. 1c.

All momenta are two-dimensional because Fig. 1c fixes the scattering plane.
The O₂ and O masses are respectively `2m` and `m`, where `atomMass` is `m`.
-/
structure OzonePhotodissociation where
  sourceFigure : SourceFigure
  ozoneGroundStateEnergy : DimEnergy
  oxygenMoleculeGroundStateEnergy : DimEnergy
  energyGap : DimEnergy
  atomMass : DimMass
  reducedPlanckConstant : DimAction
  minimumAngularFrequency : DimAngularFrequency
  thresholdPhotonEnergy : DimEnergy
  initialOzoneMomentum : DimMomentum 2
  photonMomentum : DimMomentum 2
  oxygenMoleculeMomentum : DimMomentum 2
  oxygenAtomMomentum : DimMomentum 2
  /-- The counterclockwise angle from the incident photon to outgoing O₂ in Fig. 1c. -/
  outgoingOxygenMoleculeAngleRad : ℝ

/--
The governing physical laws used in part C.

These fields expose the SI equations needed to eliminate the abstract physical
objects: the definition of `ΔU`, the photon relations `E = ℏω` and `p = E/c`,
the Fig. 1c orientation, momentum conservation, and non-relativistic energy
conservation for fragment masses `2m` and `m`.
-/
structure ClassicalPhotodissociationLaws (setup : OzonePhotodissociation) : Prop where
  source_is_figure_1c : setup.sourceFigure = .fig1c
  atom_mass_positive : 0 < massSI setup.atomMass
  reduced_planck_constant_positive : 0 < actionSI setup.reducedPlanckConstant
  minimum_frequency_nonnegative : 0 ≤ angularFrequencySI setup.minimumAngularFrequency
  energy_gap_definition :
    energySI setup.energyGap =
      energySI setup.oxygenMoleculeGroundStateEnergy -
        energySI setup.ozoneGroundStateEnergy
  threshold_photon_energy :
    energySI setup.thresholdPhotonEnergy =
      actionSI setup.reducedPlanckConstant *
        angularFrequencySI setup.minimumAngularFrequency
  ozone_initially_at_rest : momentumSI setup.initialOzoneMomentum = 0
  photon_momentum_magnitude :
    ‖momentumSI setup.photonMomentum‖ =
      energySI setup.thresholdPhotonEnergy / (DimSpeed.speedOfLight SI).val
  incident_photon_along_positive_x :
    momentumSI setup.photonMomentum 0 = ‖momentumSI setup.photonMomentum‖
  incident_photon_zero_y : momentumSI setup.photonMomentum 1 = 0
  outgoing_oxygen_molecule_nonzero :
    0 < ‖momentumSI setup.oxygenMoleculeMomentum‖
  outgoing_angle_nonnegative : 0 ≤ setup.outgoingOxygenMoleculeAngleRad
  outgoing_angle_at_most_pi :
    setup.outgoingOxygenMoleculeAngleRad ≤ Real.pi
  outgoing_oxygen_molecule_x :
    momentumSI setup.oxygenMoleculeMomentum 0 =
      ‖momentumSI setup.oxygenMoleculeMomentum‖ *
        Real.cos setup.outgoingOxygenMoleculeAngleRad
  outgoing_oxygen_molecule_y :
    momentumSI setup.oxygenMoleculeMomentum 1 =
      ‖momentumSI setup.oxygenMoleculeMomentum‖ *
        Real.sin setup.outgoingOxygenMoleculeAngleRad
  momentum_conservation :
    momentumSI setup.initialOzoneMomentum + momentumSI setup.photonMomentum =
      momentumSI setup.oxygenMoleculeMomentum + momentumSI setup.oxygenAtomMomentum
  nonrelativistic_energy_conservation :
    energySI setup.thresholdPhotonEnergy =
      energySI setup.energyGap +
        ‖momentumSI setup.oxygenMoleculeMomentum‖ ^ 2 / (4 * massSI setup.atomMass) +
        ‖momentumSI setup.oxygenAtomMomentum‖ ^ 2 / (2 * massSI setup.atomMass)

/-- Above a right angle, the C.1 threshold is the threshold at `π/2`. -/
def effectiveThresholdAngle (theta : ℝ) : ℝ := min theta (Real.pi / 2)

/-- The angular factor occurring after minimization over the fragment momentum. -/
def thresholdShapeFactor (theta : ℝ) : ℝ :=
  2 * Real.sin theta ^ 2 + 1

/--
The reusable content of part C.1, stated as the energy-balance equation for the
lower threshold root.  It is equivalent to the energy-conserving closed form and
also records the `θ ≥ π/2` branch through `effectiveThresholdAngle`.
-/
structure PreviousPartC1Threshold
    (setup : OzonePhotodissociation) : Prop where
  threshold_energy_nonnegative :
    0 ≤ energyInElectronVolts setup.thresholdPhotonEnergy
  threshold_balance :
    energyInElectronVolts setup.thresholdPhotonEnergy =
      energyInElectronVolts setup.energyGap +
        energyInElectronVolts setup.thresholdPhotonEnergy ^ 2 *
          thresholdShapeFactor
            (effectiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad) /
          (6 * restEnergyInElectronVolts setup.atomMass)
  lower_root_selection :
    energyInElectronVolts setup.thresholdPhotonEnergy ≤
      3 * restEnergyInElectronVolts setup.atomMass /
        thresholdShapeFactor
          (effectiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad)

/--
The scalar electronvolt readout of the requested quantity
`ℏ ω_min - ΔU`.
-/
def requestedExcessEnergyInElectronVolts
    (setup : OzonePhotodissociation) : ℝ :=
  actionSI setup.reducedPlanckConstant *
      angularFrequencySI setup.minimumAngularFrequency /
      energySI DimEnergy.electronVolt -
    energyInElectronVolts setup.energyGap

/--
For `θ = π/6`, `ΔU = 1.10 eV`, and `m = 16.0 amu`, the threshold excess
energy rounds to `2.03 × 10⁻¹¹ eV` to three significant figures.

The radius `5 × 10⁻¹⁴ eV` is half a unit in the last reported decimal place;
it encodes rounding of the answer, not experimental uncertainty.
-/
theorem threshold_excess_energy_rounds_to_official_value
    (setup : OzonePhotodissociation)
    (_laws : ClassicalPhotodissociationLaws setup)
    (_previousPart : PreviousPartC1Threshold setup)
    (angle_readout :
      setup.outgoingOxygenMoleculeAngleRad = Real.pi / 6)
    (energy_gap_readout :
      energyInElectronVolts setup.energyGap = 1.10)
    (atom_mass_readout :
      massInAtomicMassUnits setup.atomMass = 16.0) :
    abs (requestedExcessEnergyInElectronVolts setup - 2.03e-11) ≤ 5e-14 := by
  have hangle :
      thresholdShapeFactor
          (effectiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad) =
        3 / 2 := by
    rw [angle_readout]
    unfold effectiveThresholdAngle thresholdShapeFactor
    rw [min_eq_left (by linarith [Real.pi_pos])]
    rw [Real.sin_pi_div_six]
    norm_num
  have hamu :
      massSI atomicMassUnit =
        8302695333 / 5000000000000000000000000000000000000 := by
    norm_num [massSI, atomicMassUnit, toDimensionful_apply_apply]
  have hev :
      energySI DimEnergy.electronVolt =
        801088317 / 5000000000000000000000000000 := by
    norm_num [energySI, DimEnergy.electronVolt, toDimensionful_apply_apply]
  have hmSI :
      massSI setup.atomMass =
        16 * (8302695333 / 5000000000000000000000000000000000000) := by
    rw [massInAtomicMassUnits, hamu] at atom_mass_readout
    field_simp at atom_mass_readout
    linarith
  have hmass :
      restEnergyInElectronVolts setup.atomMass =
        62184086900064638790833951 / 4172334984375000 := by
    rw [restEnergyInElectronVolts, hmSI, hev]
    norm_num
  have hgap : energyInElectronVolts setup.energyGap = 11 / 10 := by
    norm_num at energy_gap_readout ⊢
    exact energy_gap_readout
  let x : ℝ := energyInElectronVolts setup.thresholdPhotonEnergy
  have hbalance := _previousPart.threshold_balance
  rw [hgap, hangle, hmass] at hbalance
  ring_nf at hbalance
  change
    x =
      11 / 10 +
        x ^ 2 * (1043083746093750 / 62184086900064638790833951)
    at hbalance
  have hxnonneg := _previousPart.threshold_energy_nonnegative
  change 0 ≤ x at hxnonneg
  have hlower := _previousPart.lower_root_selection
  rw [hangle, hmass] at hlower
  norm_num at hlower
  change
    x ≤ 62184086900064638790833951 / 2086167492187500
    at hlower
  have hprod :
      0 ≤
        (62184086900064638790833951 / 2086167492187500 - x) * x :=
    mul_nonneg (sub_nonneg.mpr hlower) hxnonneg
  have hxle : x ≤ 11 / 5 := by
    nlinarith [hprod]
  have hxge : 11 / 10 ≤ x := by
    nlinarith [sq_nonneg x]
  have hxsqCoarse : x ^ 2 ≤ (11 / 5 : ℝ) ^ 2 := by
    nlinarith
  have hxTight : x ≤ 11000000001 / 10000000000 := by
    nlinarith [hxsqCoarse]
  have hxsqLower : (11 / 10 : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith
  have hxsqUpper :
      x ^ 2 ≤ (11000000001 / 10000000000 : ℝ) ^ 2 := by
    nlinarith
  have hexcessLower : (2025e-14 : ℝ) ≤ x - 11 / 10 := by
    nlinarith [hxsqLower]
  have hexcessUpper : x - 11 / 10 ≤ (2035e-14 : ℝ) := by
    nlinarith [hxsqUpper]
  have hreq :
      requestedExcessEnergyInElectronVolts setup = x - 11 / 10 := by
    dsimp [x]
    rw [requestedExcessEnergyInElectronVolts,
      ← _laws.threshold_photon_energy, hgap]
    rfl
  rw [hreq, abs_le]
  constructor <;> nlinarith

end IPhO2026_1_C_2
