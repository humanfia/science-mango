import Mathlib.Algebra.Order.Round
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0557

open Dimension

/-!
# Bragg selection of thermal neutrons

A continuous beam of thermal neutrons from a reactor is Bragg scattered by a
crystal with plane spacing `0.247 nm`.  The desired outgoing neutrons have
energy `0.0105 eV`.  The angle marked `θ` in the supplied figure is the
glancing angle between either neutron ray and the scattering plane; the angle
between the incident and scattered ray directions is therefore `2 θ`.

Lengths, mass, momentum magnitude, action, energy, and the speed of light are
represented by unit-independent Physlib quantities.  Real numbers are used
only for coherent unit readouts, dimensionless angles in radians or degrees,
and displayed multiple-choice values.  In particular, the Bragg angle and
matter wavelength are independent fields of the setup and are not defined from
answer choice D.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension `M L T⁻¹` of linear momentum. -/
def momentumDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent linear-momentum magnitude. -/
abbrev MomentumMagnitude : Type :=
  Dimensionful (WithDim momentumDimension NNReal)

/-- The physical dimension `M L² T⁻¹` of action. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action, used for Planck's `h`. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- SI readout of a momentum magnitude in kilogram-metres per second. -/
def momentumInKilogramMetersPerSecond
    (momentum : MomentumMagnitude) : ℝ :=
  ((momentum UnitChoices.SI).val : ℝ)

/-- SI readout of an action in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- SI readout of a Physlib energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Electron-volt readout of an energy.  `DimEnergy.electronVolt` is itself a
dimensionful energy, so this scalar is a ratio of two same-dimensional SI
readouts rather than an alias for energy.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-!
SI readout of Physlib's dimensionful speed of light.  This is used in the
exact relativistic kinetic-energy/momentum law, avoiding an unbounded
nonrelativistic approximation.
-/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Convert a dimensionless angular readout in radians to degrees. -/
def angleInDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-! ## Physical roles and primary-figure vocabulary -/

/-- Particle species carried by the reactor beam. -/
inductive ParticleSpecies where
  | neutron
  | other
  deriving DecidableEq, Repr

/-- Energy-spectrum regime of the incident source. -/
inductive BeamSpectrum where
  | continuousThermal
  | other
  deriving DecidableEq, Repr

/-- Physical scattering regime used by the model. -/
inductive ScatteringRegime where
  | elasticBragg
  | other
  deriving DecidableEq, Repr

/-- Labeled apparatus components visible in the supplied schematic. -/
inductive ApparatusComponent where
  | reactor
  | shielding
  | graphite
  | scatteringCrystal
  deriving DecidableEq, Fintype, Repr

/-- The two directed neutron-ray segments shown at the crystal. -/
inductive FigureRay where
  | incidentNeutronBeam
  | scatteredNeutronBeam
  deriving DecidableEq, Fintype, Repr

/-- The two angle marks drawn on opposite sides of the crystal plane. -/
inductive FigureAngleMark where
  | incidentGlancingAngle
  | scatteredGlancingAngle
  deriving DecidableEq, Fintype, Repr

/-- Geometric role of an angle annotation in the schematic. -/
inductive FigureAngleRole where
  | betweenIncidentRayAndCrystalPlane
  | betweenScatteredRayAndCrystalPlane
  deriving DecidableEq, Repr

/-- The Greek symbol printed beside either glancing-angle arc. -/
inductive FigureAngleSymbol where
  | theta
  deriving DecidableEq, Repr

/-!
Qualitative information and symbolic angle denotations read from image 557.
The image is schematic, so it supplies no numerical angular measurement.
-/
structure ReactorCrystalFigure where
  componentShown : ApparatusComponent → Bool
  componentHasPrintedName : ApparatusComponent → Bool
  rayShown : FigureRay → Bool
  rayHasArrowHead : FigureRay → Bool
  angleRole : FigureAngleMark → FigureAngleRole
  angleSymbol : FigureAngleMark → FigureAngleSymbol
  angleDenotationRadians : FigureAngleMark → ℝ
  reactorIsLeftOfShielding : Bool
  graphiteIsInsideShielding : Bool
  incidentRayEmergesFromGraphite : Bool
  incidentRayTerminatesAtCrystal : Bool
  scatteredRayEmergesFromCrystal : Bool
  crystalPlaneIsDrawnTilted : Bool
  neutronBeamLabelShown : Bool

/-!
The independent physical objects and observables in the experiment.  The
selected kinetic energy is the requested spectral component; the incident and
scattered kinetic energies are kept separate so that elastic scattering is a
law rather than a definition.
-/
structure ThermalNeutronBraggSetup where
  particleSpecies : ParticleSpecies
  sourceSpectrum : BeamSpectrum
  regime : ScatteringRegime
  crystalPlaneSpacing : LengthQuantity
  selectedNeutronKineticEnergy : DimEnergy
  incidentNeutronKineticEnergy : DimEnergy
  scatteredNeutronKineticEnergy : DimEnergy
  neutronMass : MassQuantity
  scatteredMomentumMagnitude : MomentumMagnitude
  ordinaryPlanckAction : ActionQuantity
  scatteredMatterWavelength : LengthQuantity
  braggOrder : ℕ
  braggAngleRadians : ℝ
  scatteringDeflectionRadians : ℝ
  figure : ReactorCrystalFigure
  reactorEmitsBeam : Bool
  shieldingSurroundsBeamExit : Bool
  graphiteModeratesBeam : Bool
  beamIsIncidentOnCrystal : Bool
  outgoingBeamIsBraggScattered : Bool

/-! ## Scenario, data readouts, reference data, and governing physics -/

/-!
The qualitative reactor/crystal scenario.  The equality selecting the desired
outgoing energy is physical setup data and contains no diffraction order,
angular value, or answer label.
-/
structure MatchesThermalNeutronBraggScenario
    (setup : ThermalNeutronBraggSetup) : Prop where
  particleIsNeutron : setup.particleSpecies = .neutron
  spectrumIsContinuousAndThermal : setup.sourceSpectrum = .continuousThermal
  usesElasticBraggRegime : setup.regime = .elasticBragg
  reactorIsSource : setup.reactorEmitsBeam = true
  shieldingAtBeamExit : setup.shieldingSurroundsBeamExit = true
  graphiteIsModerator : setup.graphiteModeratesBeam = true
  beamReachesCrystal : setup.beamIsIncidentOnCrystal = true
  outgoingBeamIsDiffracted : setup.outgoingBeamIsBraggScattered = true
  scatteredBeamHasSelectedKineticEnergy :
    setup.scatteredNeutronKineticEnergy = setup.selectedNeutronKineticEnergy

/-!
The two quantitative readouts stated in the prose.  Neither readout mentions
the unknown matter wavelength, Bragg angle, deflection, or answer choice.
-/
structure MatchesProblemReadouts (setup : ThermalNeutronBraggSetup) : Prop where
  planeSpacingNanometers :
    lengthInNanometers setup.crystalPlaneSpacing = 0.247
  selectedKineticEnergyElectronVolts :
    energyInElectronVolts setup.selectedNeutronKineticEnergy = 0.0105

/-!
Exact qualitative labels and ray geometry transcribed from the primary image.
Both arcs carry the same symbolic `θ`; their denotations are connected to the
setup's unknown Bragg angle without supplying a numerical angle.
-/
structure MatchesSuppliedReactorCrystalFigure
    (setup : ThermalNeutronBraggSetup) : Prop where
  everyComponentIsShown :
    ∀ component, setup.figure.componentShown component = true
  everyComponentIsNamed :
    ∀ component, setup.figure.componentHasPrintedName component = true
  bothNeutronRaysAreShown :
    ∀ ray, setup.figure.rayShown ray = true
  bothNeutronRaysHaveArrowHeads :
    ∀ ray, setup.figure.rayHasArrowHead ray = true
  incidentAngleRole :
    setup.figure.angleRole .incidentGlancingAngle =
      .betweenIncidentRayAndCrystalPlane
  scatteredAngleRole :
    setup.figure.angleRole .scatteredGlancingAngle =
      .betweenScatteredRayAndCrystalPlane
  incidentAngleMarkedTheta :
    setup.figure.angleSymbol .incidentGlancingAngle = .theta
  scatteredAngleMarkedTheta :
    setup.figure.angleSymbol .scatteredGlancingAngle = .theta
  incidentThetaDenotesBraggAngle :
    setup.figure.angleDenotationRadians .incidentGlancingAngle =
      setup.braggAngleRadians
  scatteredThetaDenotesBraggAngle :
    setup.figure.angleDenotationRadians .scatteredGlancingAngle =
      setup.braggAngleRadians
  reactorAtLeft : setup.figure.reactorIsLeftOfShielding = true
  graphiteWithinShield : setup.figure.graphiteIsInsideShielding = true
  incidentBeamEmergesFromGraphite :
    setup.figure.incidentRayEmergesFromGraphite = true
  incidentBeamMeetsCrystal :
    setup.figure.incidentRayTerminatesAtCrystal = true
  scatteredBeamLeavesCrystal :
    setup.figure.scatteredRayEmergesFromCrystal = true
  tiltedCrystalPlaneShown : setup.figure.crystalPlaneIsDrawnTilted = true
  neutronBeamIsLabeled : setup.figure.neutronBeamLabelShown = true

/-!
Standard numerical reference data.  Physlib supplies the reduced Planck
constant in joule-seconds and a dimensionful speed of light; ordinary Planck
action is `h = 2πℏ`.  LeanExplore did not expose a standard neutron-mass
declaration, so its SI calibration is stated explicitly here.  Neither datum
contains the requested angle.
-/
structure UsesStandardNeutronReferenceData
    (setup : ThermalNeutronBraggSetup) : Prop where
  neutronMassKilograms :
    massInKilograms setup.neutronMass = 1.67492749804e-27
  ordinaryPlanckActionJouleSeconds :
    actionInJouleSeconds setup.ordinaryPlanckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-!
Domain conditions selecting positive physical magnitudes and the principal
glancing-angle branch `0 < θ < π/2`.  These conditions contain no numerical
degree result or answer choice.
-/
structure HasPhysicalBraggParameters
    (setup : ThermalNeutronBraggSetup) : Prop where
  planeSpacingPositive : 0 < lengthInMeters setup.crystalPlaneSpacing
  selectedKineticEnergyPositive :
    0 < energyInJoules setup.selectedNeutronKineticEnergy
  incidentKineticEnergyPositive :
    0 < energyInJoules setup.incidentNeutronKineticEnergy
  scatteredKineticEnergyPositive :
    0 < energyInJoules setup.scatteredNeutronKineticEnergy
  neutronMassPositive : 0 < massInKilograms setup.neutronMass
  momentumMagnitudePositive :
    0 < momentumInKilogramMetersPerSecond setup.scatteredMomentumMagnitude
  planckActionPositive :
    0 < actionInJouleSeconds setup.ordinaryPlanckAction
  matterWavelengthPositive :
    0 < lengthInMeters setup.scatteredMatterWavelength
  diffractionOrderPositive : 0 < setup.braggOrder
  braggAnglePositive : 0 < setup.braggAngleRadians
  braggAngleAcute : setup.braggAngleRadians < Real.pi / 2

/-!
The exact governing relations used in the calculation:

* elastic crystal scattering conserves the neutron energy;
* relativistic kinetic energy `K` and momentum obey
  `(p c)² = K² + 2 K m c²`;
* de Broglie's law obeys `λ p = h`;
* Bragg's law obeys `n λ = 2 d sin θ`;
* the figure's total ray deflection is twice its glancing angle.

All products use coherent SI readouts.  These laws relate independent fields
and are not specialized to `34.4°` or any displayed choice.  In particular,
the dispersion relation is exact rather than a nonrelativistic equality
globalized by a regime tag.
-/
structure SatisfiesThermalNeutronBraggLaws
    (setup : ThermalNeutronBraggSetup) : Prop where
  elasticEnergyConservation :
    energyInJoules setup.incidentNeutronKineticEnergy =
      energyInJoules setup.scatteredNeutronKineticEnergy
  relativisticKineticEnergyMomentumLaw :
    (momentumInKilogramMetersPerSecond setup.scatteredMomentumMagnitude *
        speedOfLightInMetersPerSecond) ^ 2 =
      energyInJoules setup.scatteredNeutronKineticEnergy ^ 2 +
        2 * energyInJoules setup.scatteredNeutronKineticEnergy *
          massInKilograms setup.neutronMass *
            speedOfLightInMetersPerSecond ^ 2
  deBroglieMatterWaveLaw :
    lengthInMeters setup.scatteredMatterWavelength *
        momentumInKilogramMetersPerSecond setup.scatteredMomentumMagnitude =
      actionInJouleSeconds setup.ordinaryPlanckAction
  braggDiffractionLaw :
    (setup.braggOrder : ℝ) *
        lengthInMeters setup.scatteredMatterWavelength =
      2 * lengthInMeters setup.crystalPlaneSpacing *
        Real.sin setup.braggAngleRadians
  specularFigureGeometry :
    setup.scatteringDeflectionRadians = 2 * setup.braggAngleRadians

/-! ## Displayed answers and derived target -/

/-- Labels of the four angular choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Angle in degrees printed beside each answer label. -/
def AnswerChoice.angleDegrees : AnswerChoice → ℝ
  | .A => 12.7
  | .B => 62.3
  | .C => 38.1
  | .D => 34.4

/-- Dataset metadata records answer D; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- `value` rounds to the displayed angular value at one decimal place. -/
def RoundsToOneDecimalDegree (value displayed : ℝ) : Prop :=
  ((round (10 * value) : ℤ) : ℝ) / 10 = displayed

/-- A displayed choice agrees with the modeled glancing angle after rounding. -/
def MatchesDisplayedBraggAngle
    (setup : ThermalNeutronBraggSetup) (choice : AnswerChoice) : Prop :=
  RoundsToOneDecimalDegree
    (angleInDegrees setup.braggAngleRadians)
    choice.angleDegrees

/-- A choice is the unique displayed angle matching the modeled result. -/
def IsUniqueMatchingDisplayedBraggAngle
    (setup : ThermalNeutronBraggSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedBraggAngle setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedBraggAngle setup other → other = choice

/-!
The energy, standard neutron mass, and de Broglie relation put the selected
neutron wavelength between `0.278 nm` and `0.280 nm`.
-/
lemma selected_neutron_wavelength_nanometers_in_interval
    (setup : ThermalNeutronBraggSetup)
    (hScenario : MatchesThermalNeutronBraggScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesStandardNeutronReferenceData setup)
    (hPhysical : HasPhysicalBraggParameters setup)
    (hLaws : SatisfiesThermalNeutronBraggLaws setup) :
    0.278 < lengthInNanometers setup.scatteredMatterWavelength ∧
      lengthInNanometers setup.scatteredMatterWavelength < 0.280 := by
  have length_nm_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    let nmUnits : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.nanometers}
    have hScale :
        UnitChoices.SI.dimScale nmUnits L𝓭 = (1000000000 : NNReal) := by
      dsimp [nmUnits]
      simp [UnitChoices.dimScale, LengthUnit.nanometers]
      apply Subtype.ext
      norm_num
    have h := length.2 UnitChoices.SI nmUnits
    have h' := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInNanometers length = _ at h'
    rw [h']
    simp only [WithDim.dim_apply]
    rw [hScale]
    simp [lengthInMeters, lengthReadout]
    change (length UnitChoices.SI).val = (length UnitChoices.SI).val
    rfl
  have hElectronVolt :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hSelectedEnergy :
      energyInJoules setup.selectedNeutronKineticEnergy =
        0.0105 * 1.602176634e-19 := by
    have h := hReadouts.selectedKineticEnergyElectronVolts
    rw [energyInElectronVolts, hElectronVolt] at h
    norm_num at h ⊢
    nlinarith
  have hScatteredEnergy :
      energyInJoules setup.scatteredNeutronKineticEnergy =
        0.0105 * 1.602176634e-19 := by
    rw [hScenario.scatteredBeamHasSelectedKineticEnergy]
    exact hSelectedEnergy
  have hSpeedOfLight :
      speedOfLightInMetersPerSecond = 299792458 := by
    simp [speedOfLightInMetersPerSecond]
  let q : ℝ :=
    momentumInKilogramMetersPerSecond setup.scatteredMomentumMagnitude *
      10 ^ 24
  have hq_pos : 0 < q := by
    dsimp [q]
    exact mul_pos hPhysical.momentumMagnitudePositive (by norm_num)
  have hMomentumLaw := hLaws.relativisticKineticEnergyMomentumLaw
  rw [hScatteredEnergy, hReference.neutronMassKilograms, hSpeedOfLight] at hMomentumLaw
  have hq_lower : (2.373 : ℝ) < q := by
    dsimp [q]
    nlinarith
  have hq_upper : q < (2.38 : ℝ) := by
    dsimp [q]
    nlinarith
  have hPlanckAction :
      actionInJouleSeconds setup.ordinaryPlanckAction =
        2 * Real.pi * 1.054571817e-34 := by
    simpa [Constants.ℏ] using
      hReference.ordinaryPlanckActionJouleSeconds
  have hScaledDeBroglie :
      lengthInNanometers setup.scatteredMatterWavelength * q =
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    calc
      lengthInNanometers setup.scatteredMatterWavelength * q =
          (1000000000 *
              lengthInMeters setup.scatteredMatterWavelength) *
            (momentumInKilogramMetersPerSecond
                setup.scatteredMomentumMagnitude * 10 ^ 24) := by
        rw [length_nm_eq]
      _ = (lengthInMeters setup.scatteredMatterWavelength *
              momentumInKilogramMetersPerSecond
                setup.scatteredMomentumMagnitude) * 10 ^ 33 := by
        ring
      _ = actionInJouleSeconds setup.ordinaryPlanckAction * 10 ^ 33 := by
        rw [hLaws.deBroglieMatterWaveLaw]
      _ = (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
        rw [hPlanckAction]
  have sin_lt_local {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx_one | hx_one
    · exact (Real.sin_le_one x).trans_lt hx_one
    have hx_abs : |x| = x := abs_of_nonneg hx.le
    have h_bound :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx_abs]))
    rw [sub_le_iff_le_add', hx_abs] at h_bound
    apply h_bound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp
  have hSeriesUpper :
      Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := by
    have h₁ : √(2 : ℝ) ≤ (338 : ℝ) / 239 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : √(2 + √(2 : ℝ)) ≤ (704 : ℝ) / 381 := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        √(2 + √(2 + √(2 : ℝ))) ≤ (1940 : ℝ) / 989 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        √(2 + √(2 + √(2 + √(2 : ℝ)))) ≤
          (1447 : ℝ) / 727 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄
  have hSeriesLower :
      (412 : ℝ) / 207 ≤ Real.sqrtTwoAddSeries 0 4 := by
    have h₁ : (41 : ℝ) / 29 ≤ √(2 : ℝ) := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : (109 : ℝ) / 59 ≤ √(2 + √(2 : ℝ)) := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        (865 : ℝ) / 441 ≤ √(2 + √(2 + √(2 : ℝ))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        (412 : ℝ) / 207 ≤
          √(2 + √(2 + √(2 + √(2 : ℝ)))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    have hSinLower :
        (3.14 : ℝ) / 64 < Real.sin (Real.pi / 64) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [hSeriesUpper, hsq, hnonneg]
    have hSinUpper :=
      sin_lt_local (show 0 < Real.pi / 64 by positivity)
    nlinarith only [hSinLower, hSinUpper]
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    have hSinUpper :
        Real.sin (Real.pi / 64) < (0.04916 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [hSeriesLower, hsq, hnonneg]
    let x : ℝ := Real.pi / 64
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hx_le : x ≤ (1 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [Real.pi_le_four]
    have hx_abs : |x| = x := abs_of_pos hx_pos
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (x := x) (by rw [hx_abs]; linarith only [hx_le]))
    rw [hx_abs] at hBound
    have hx3 : x ^ 3 ≤ ((1 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hx_pos.le hx_le 3
    have hx4 : x ^ 4 ≤ ((1 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_pos.le hx_le 4
    have hSinX : Real.sin x < (0.04916 : ℝ) := by
      simpa [x] using hSinUpper
    dsimp [x] at hBound hx3 hx4 hSinX ⊢
    nlinarith only [hBound, hx3, hx4, hSinX]
  have hScaledActionLower :
      (0.662 : ℝ) <
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    nlinarith only [hPiLower]
  have hScaledActionUpper :
      (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 <
        (0.6644 : ℝ) := by
    nlinarith only [hPiUpper]
  constructor
  · by_contra h
    have hWavelengthUpper :
        lengthInNanometers setup.scatteredMatterWavelength ≤ 0.278 :=
      le_of_not_gt h
    have hProductUpper :
        lengthInNanometers setup.scatteredMatterWavelength * q <
          (0.278 : ℝ) * 2.38 :=
      (mul_le_mul_of_nonneg_right hWavelengthUpper hq_pos.le).trans_lt
        (mul_lt_mul_of_pos_left hq_upper (by norm_num))
    rw [hScaledDeBroglie] at hProductUpper
    norm_num at hProductUpper
    linarith
  · by_contra h
    have hWavelengthLower :
        0.280 ≤ lengthInNanometers setup.scatteredMatterWavelength :=
      le_of_not_gt h
    have hProductLower :
        (0.280 : ℝ) * 2.373 <
          lengthInNanometers setup.scatteredMatterWavelength * q :=
      (mul_lt_mul_of_pos_left hq_lower (by norm_num)).trans_le
        (mul_le_mul_of_nonneg_right hWavelengthLower hq_pos.le)
    rw [hScaledDeBroglie] at hProductLower
    norm_num at hProductLower
    linarith

/-!
For this wavelength and plane spacing, every positive diffraction order above
one would make the Bragg-law sine exceed one.  Thus first order is derived
from the physical branch rather than inserted as source data.
-/
lemma bragg_order_eq_one
    (setup : ThermalNeutronBraggSetup)
    (hScenario : MatchesThermalNeutronBraggScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesStandardNeutronReferenceData setup)
    (hPhysical : HasPhysicalBraggParameters setup)
    (hLaws : SatisfiesThermalNeutronBraggLaws setup) :
    setup.braggOrder = 1 := by
  have length_nm_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    let nmUnits : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.nanometers}
    have hScale :
        UnitChoices.SI.dimScale nmUnits L𝓭 = (1000000000 : NNReal) := by
      dsimp [nmUnits]
      simp [UnitChoices.dimScale, LengthUnit.nanometers]
      apply Subtype.ext
      norm_num
    have h := length.2 UnitChoices.SI nmUnits
    have h' := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInNanometers length = _ at h'
    rw [h']
    simp only [WithDim.dim_apply]
    rw [hScale]
    simp [lengthInMeters, lengthReadout]
    change (length UnitChoices.SI).val = (length UnitChoices.SI).val
    rfl
  have hWavelength :=
    selected_neutron_wavelength_nanometers_in_interval
      setup hScenario hReadouts hReference hPhysical hLaws
  have hBraggNanometers :
      (setup.braggOrder : ℝ) *
          lengthInNanometers setup.scatteredMatterWavelength =
        2 * lengthInNanometers setup.crystalPlaneSpacing *
          Real.sin setup.braggAngleRadians := by
    calc
      (setup.braggOrder : ℝ) *
          lengthInNanometers setup.scatteredMatterWavelength =
          (setup.braggOrder : ℝ) *
            (1000000000 *
              lengthInMeters setup.scatteredMatterWavelength) := by
        rw [length_nm_eq]
      _ = 1000000000 *
          ((setup.braggOrder : ℝ) *
            lengthInMeters setup.scatteredMatterWavelength) := by
        ring
      _ = 1000000000 *
          (2 * lengthInMeters setup.crystalPlaneSpacing *
            Real.sin setup.braggAngleRadians) := by
        rw [hLaws.braggDiffractionLaw]
      _ = 2 *
          (1000000000 * lengthInMeters setup.crystalPlaneSpacing) *
            Real.sin setup.braggAngleRadians := by
        ring
      _ = 2 * lengthInNanometers setup.crystalPlaneSpacing *
          Real.sin setup.braggAngleRadians := by
        rw [length_nm_eq]
  by_contra hOrder
  have hOrderNat : 2 ≤ setup.braggOrder := by
    have hOrderPositive := hPhysical.diffractionOrderPositive
    omega
  have hOrderReal : (2 : ℝ) ≤ setup.braggOrder := by
    exact_mod_cast hOrderNat
  have hOrderProduct :
      0 ≤ ((setup.braggOrder : ℝ) - 2) *
        lengthInNanometers setup.scatteredMatterWavelength :=
    mul_nonneg (sub_nonneg.mpr hOrderReal) (by
      linarith only [hWavelength.1])
  rw [hReadouts.planeSpacingNanometers] at hBraggNanometers
  have hSinUpper := Real.sin_le_one setup.braggAngleRadians
  nlinarith only [hWavelength.1, hBraggNanometers, hSinUpper,
    hOrderProduct]

/-!
The only possible positive order is first order, so on the acute branch
Bragg's law puts the figure's `θ` in the one-decimal-degree interval that
rounds to `34.4°`.
-/
lemma bragg_angle_degrees_in_rounding_interval
    (setup : ThermalNeutronBraggSetup)
    (hScenario : MatchesThermalNeutronBraggScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesStandardNeutronReferenceData setup)
    (hPhysical : HasPhysicalBraggParameters setup)
    (hLaws : SatisfiesThermalNeutronBraggLaws setup) :
    34.35 ≤ angleInDegrees setup.braggAngleRadians ∧
      angleInDegrees setup.braggAngleRadians < 34.45 := by
  have length_nm_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    let nmUnits : UnitChoices :=
      {UnitChoices.SI with length := LengthUnit.nanometers}
    have hScale :
        UnitChoices.SI.dimScale nmUnits L𝓭 = (1000000000 : NNReal) := by
      dsimp [nmUnits]
      simp [UnitChoices.dimScale, LengthUnit.nanometers]
      apply Subtype.ext
      norm_num
    have h := length.2 UnitChoices.SI nmUnits
    have h' := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInNanometers length = _ at h'
    rw [h']
    simp only [WithDim.dim_apply]
    rw [hScale]
    simp [lengthInMeters, lengthReadout]
    change (length UnitChoices.SI).val = (length UnitChoices.SI).val
    rfl
  have hElectronVolt :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hSelectedEnergy :
      energyInJoules setup.selectedNeutronKineticEnergy =
        0.0105 * 1.602176634e-19 := by
    have h := hReadouts.selectedKineticEnergyElectronVolts
    rw [energyInElectronVolts, hElectronVolt] at h
    norm_num at h ⊢
    nlinarith
  have hScatteredEnergy :
      energyInJoules setup.scatteredNeutronKineticEnergy =
        0.0105 * 1.602176634e-19 := by
    rw [hScenario.scatteredBeamHasSelectedKineticEnergy]
    exact hSelectedEnergy
  have hSpeedOfLight :
      speedOfLightInMetersPerSecond = 299792458 := by
    simp [speedOfLightInMetersPerSecond]
  let q : ℝ :=
    momentumInKilogramMetersPerSecond setup.scatteredMomentumMagnitude *
      10 ^ 24
  have hq_pos : 0 < q := by
    dsimp [q]
    exact mul_pos hPhysical.momentumMagnitudePositive (by norm_num)
  have hMomentumLaw := hLaws.relativisticKineticEnergyMomentumLaw
  rw [hScatteredEnergy, hReference.neutronMassKilograms, hSpeedOfLight] at hMomentumLaw
  have hq_lower : (2.3738 : ℝ) < q := by
    dsimp [q]
    nlinarith
  have hq_upper : q < (2.374 : ℝ) := by
    dsimp [q]
    nlinarith
  have hPlanckAction :
      actionInJouleSeconds setup.ordinaryPlanckAction =
        2 * Real.pi * 1.054571817e-34 := by
    simpa [Constants.ℏ] using
      hReference.ordinaryPlanckActionJouleSeconds
  have hScaledDeBroglie :
      lengthInNanometers setup.scatteredMatterWavelength * q =
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    calc
      lengthInNanometers setup.scatteredMatterWavelength * q =
          (1000000000 *
              lengthInMeters setup.scatteredMatterWavelength) *
            (momentumInKilogramMetersPerSecond
                setup.scatteredMomentumMagnitude * 10 ^ 24) := by
        rw [length_nm_eq]
      _ = (lengthInMeters setup.scatteredMatterWavelength *
              momentumInKilogramMetersPerSecond
                setup.scatteredMomentumMagnitude) * 10 ^ 33 := by
        ring
      _ = actionInJouleSeconds setup.ordinaryPlanckAction * 10 ^ 33 := by
        rw [hLaws.deBroglieMatterWaveLaw]
      _ = (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
        rw [hPlanckAction]
  have hBraggNanometers :
      (setup.braggOrder : ℝ) *
          lengthInNanometers setup.scatteredMatterWavelength =
        2 * lengthInNanometers setup.crystalPlaneSpacing *
          Real.sin setup.braggAngleRadians := by
    calc
      (setup.braggOrder : ℝ) *
          lengthInNanometers setup.scatteredMatterWavelength =
          (setup.braggOrder : ℝ) *
            (1000000000 *
              lengthInMeters setup.scatteredMatterWavelength) := by
        rw [length_nm_eq]
      _ = 1000000000 *
          ((setup.braggOrder : ℝ) *
            lengthInMeters setup.scatteredMatterWavelength) := by
        ring
      _ = 1000000000 *
          (2 * lengthInMeters setup.crystalPlaneSpacing *
            Real.sin setup.braggAngleRadians) := by
        rw [hLaws.braggDiffractionLaw]
      _ = 2 *
          (1000000000 * lengthInMeters setup.crystalPlaneSpacing) *
            Real.sin setup.braggAngleRadians := by
        ring
      _ = 2 * lengthInNanometers setup.crystalPlaneSpacing *
          Real.sin setup.braggAngleRadians := by
        rw [length_nm_eq]
  have hOrder :=
    bragg_order_eq_one setup hScenario hReadouts hReference hPhysical hLaws
  rw [hOrder, hReadouts.planeSpacingNanometers] at hBraggNanometers
  norm_num at hBraggNanometers
  have hSineEquation :
      (0.494 * Real.sin setup.braggAngleRadians) * q =
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    rw [← hScaledDeBroglie]
    rw [hBraggNanometers]
    norm_num
  have hSinPiThirtyTwoBounds :
      (0.09801 : ℝ) < Real.sin (Real.pi / 32) ∧
        Real.sin (Real.pi / 32) < (0.09802 : ℝ) := by
    have hr2Lower : (1.41421 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hr2Upper : Real.sqrt 2 < (1.41422 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hr3Lower :
        (1.847757 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num at ⊢
      linarith
    have hr3Upper :
        Real.sqrt (2 + Real.sqrt 2) < (1.847762 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num at ⊢
      linarith
    have hr4Lower :
        (1.961570 : ℝ) <
          Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num at ⊢
      linarith
    have hr4Upper :
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
          (1.961572 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num at ⊢
      linarith
    have hsLower :
        (0.19603 : ℝ) <
          Real.sqrt
            (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num at ⊢
      linarith
    have hsUpper :
        Real.sqrt
            (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
          (0.19604 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num at ⊢
      linarith
    rw [Real.sin_pi_div_thirty_two]
    constructor <;> linarith
  have hPiBounds :
      (3.141 : ℝ) < Real.pi ∧ Real.pi < (3.142 : ℝ) := by
    let x : ℝ := Real.pi / 32
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      positivity
    have hx3_nonneg : 0 ≤ x ^ 3 := pow_nonneg hx_nonneg _
    have hx_le_eighth : x ≤ (1 / 8 : ℝ) := by
      dsimp [x]
      linarith [Real.pi_le_four]
    have hx_abs : |x| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hsinApprox := Real.sin_bound hx_abs
    rw [abs_of_nonneg hx_nonneg] at hsinApprox
    have happroxLower := (abs_le.mp hsinApprox).1
    have happroxUpper := (abs_le.mp hsinApprox).2
    constructor
    · by_contra h
      have hxUpper : x ≤ (3.141 / 32 : ℝ) := by
        dsimp [x]
        linarith
      have hxUpper' : x ≤ (1 / 10 : ℝ) := by
        linarith
      have hx4Upper : x ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hxUpper' 4
      have hxLower : (0.097 : ℝ) ≤ x := by
        by_contra hx
        have hx' : x < (0.097 : ℝ) := lt_of_not_ge hx
        have hsinLower := hSinPiThirtyTwoBounds.1
        change Real.sin x > (0.09801 : ℝ) at hsinLower
        norm_num at hx4Upper
        linarith
      have hx3Lower : (0.097 : ℝ) ^ 3 ≤ x ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hxLower 3
      have hsinLower := hSinPiThirtyTwoBounds.1
      change Real.sin x > (0.09801 : ℝ) at hsinLower
      norm_num at hx3Lower hx4Upper
      linarith
    · by_contra h
      have hxLower : (3.142 / 32 : ℝ) ≤ x := by
        dsimp [x]
        linarith
      have hxUpper : x ≤ (0.099 : ℝ) := by
        by_contra hx
        have hx' : (0.099 : ℝ) < x := lt_of_not_ge hx
        have hx3Upper : x ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hx_nonneg hx_le_eighth 3
        have hx4Upper : x ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hx_nonneg hx_le_eighth 4
        have hsinUpper := hSinPiThirtyTwoBounds.2
        change Real.sin x < (0.09802 : ℝ) at hsinUpper
        norm_num at hx3Upper hx4Upper
        linarith
      have hx3Upper : x ^ 3 ≤ (0.099 : ℝ) ^ 3 :=
        pow_le_pow_left₀ hx_nonneg hxUpper 3
      have hx4Upper : x ^ 4 ≤ (0.099 : ℝ) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hxUpper 4
      have hsinUpper := hSinPiThirtyTwoBounds.2
      change Real.sin x < (0.09802 : ℝ) at hsinUpper
      norm_num at hx3Upper hx4Upper
      linarith
  have hScaledActionLower :
      (0.66247 : ℝ) <
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    nlinarith only [hPiBounds.1]
  have hScaledActionUpper :
      (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 <
        (0.6627 : ℝ) := by
    nlinarith only [hPiBounds.2]
  have hSinThetaPositive :
      0 < Real.sin setup.braggAngleRadians := by
    apply Real.sin_pos_of_pos_of_lt_pi hPhysical.braggAnglePositive
    nlinarith only [hPhysical.braggAngleAcute, Real.pi_pos]
  have hSinThetaLower :
      (0.56485 : ℝ) < Real.sin setup.braggAngleRadians := by
    by_contra h
    have hSinThetaUpper :
        Real.sin setup.braggAngleRadians ≤ 0.56485 :=
      le_of_not_gt h
    have hProductUpper :
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 <
          (0.66247 : ℝ) := by
      calc
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 =
            (0.494 * Real.sin setup.braggAngleRadians) * q :=
          hSineEquation.symm
        _ ≤ (0.494 * 0.56485) * q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSinThetaUpper (by norm_num))
            hq_pos.le
        _ < (0.494 * 0.56485) * 2.374 :=
          mul_lt_mul_of_pos_left hq_upper (by norm_num)
        _ < (0.66247 : ℝ) := by norm_num
    linarith
  have hSinThetaUpper :
      Real.sin setup.braggAngleRadians < (0.56515 : ℝ) := by
    by_contra h
    have hSinThetaLower :
        0.56515 ≤ Real.sin setup.braggAngleRadians :=
      le_of_not_gt h
    have hProductLower :
        (0.6627 : ℝ) <
          (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
      calc
        (0.6627 : ℝ) < (0.494 * 0.56515) * 2.3738 := by
          norm_num
        _ < (0.494 * 0.56515) * q :=
          mul_lt_mul_of_pos_left hq_lower (by norm_num)
        _ ≤ (0.494 * Real.sin setup.braggAngleRadians) * q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSinThetaLower (by norm_num))
            hq_pos.le
        _ = (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 :=
          hSineEquation
    linarith
  have hSqrtThreeLower : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtThreeUpper : Real.sqrt 3 < (1.733 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  let deltaLower : ℝ := 29 * Real.pi / 1200
  have hDeltaLowerPositive : 0 < deltaLower := by
    dsimp [deltaLower]
    positivity
  have hDeltaLowerLower : (0.0759 : ℝ) < deltaLower := by
    dsimp [deltaLower]
    nlinarith only [hPiBounds.1]
  have hDeltaLowerUpper : deltaLower < (0.07594 : ℝ) := by
    dsimp [deltaLower]
    nlinarith only [hPiBounds.2]
  have hDeltaLowerAbs : |deltaLower| ≤ 1 := by
    rw [abs_of_pos hDeltaLowerPositive]
    linarith only [hDeltaLowerUpper]
  have hDeltaLowerSqLower :
      (0.0759 : ℝ) ^ 2 ≤ deltaLower ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hDeltaLowerLower.le 2
  have hDeltaLowerCubeLower :
      (0.0759 : ℝ) ^ 3 ≤ deltaLower ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hDeltaLowerLower.le 3
  have hDeltaLowerFourthUpper :
      deltaLower ^ 4 ≤ (0.07594 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hDeltaLowerPositive.le hDeltaLowerUpper.le 4
  have hSinDeltaLowerUpper :
      Real.sin deltaLower < (0.07587 : ℝ) := by
    have hApprox := (abs_le.mp (Real.sin_bound hDeltaLowerAbs)).2
    rw [abs_of_pos hDeltaLowerPositive] at hApprox
    nlinarith only [hApprox, hDeltaLowerUpper,
      hDeltaLowerCubeLower, hDeltaLowerFourthUpper]
  have hCosDeltaLowerUpper :
      Real.cos deltaLower < (0.99713 : ℝ) := by
    have hApprox := (abs_le.mp (Real.cos_bound hDeltaLowerAbs)).2
    rw [abs_of_pos hDeltaLowerPositive] at hApprox
    nlinarith only [hApprox, hDeltaLowerSqLower,
      hDeltaLowerFourthUpper]
  have hSinDeltaLowerPositive : 0 < Real.sin deltaLower := by
    apply Real.sin_pos_of_pos_of_lt_pi hDeltaLowerPositive
    dsimp [deltaLower]
    nlinarith only [Real.pi_pos]
  have hSqrtSinLowerProduct :
      Real.sqrt 3 * Real.sin deltaLower <
        (1.733 : ℝ) * 0.07587 :=
    mul_lt_mul hSqrtThreeUpper hSinDeltaLowerUpper.le
      hSinDeltaLowerPositive (by norm_num)
  have hLowerEndpointSine :
      Real.sin ((34.35 : ℝ) * Real.pi / 180) < (0.56485 : ℝ) := by
    have hAngle :
        (34.35 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + deltaLower := by
      dsimp [deltaLower]
      ring
    rw [hAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hCosDeltaLowerUpper, hSqrtSinLowerProduct]
  let deltaUpper : ℝ := 89 * Real.pi / 3600
  have hDeltaUpperPositive : 0 < deltaUpper := by
    dsimp [deltaUpper]
    positivity
  have hDeltaUpperLower : (0.07765 : ℝ) < deltaUpper := by
    dsimp [deltaUpper]
    nlinarith only [hPiBounds.1]
  have hDeltaUpperUpper : deltaUpper < (0.07768 : ℝ) := by
    dsimp [deltaUpper]
    nlinarith only [hPiBounds.2]
  have hDeltaUpperAbs : |deltaUpper| ≤ 1 := by
    rw [abs_of_pos hDeltaUpperPositive]
    linarith only [hDeltaUpperUpper]
  have hDeltaUpperSqUpper :
      deltaUpper ^ 2 ≤ (0.07768 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hDeltaUpperPositive.le hDeltaUpperUpper.le 2
  have hDeltaUpperCubeUpper :
      deltaUpper ^ 3 ≤ (0.07768 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hDeltaUpperPositive.le hDeltaUpperUpper.le 3
  have hDeltaUpperFourthUpper :
      deltaUpper ^ 4 ≤ (0.07768 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hDeltaUpperPositive.le hDeltaUpperUpper.le 4
  have hSinDeltaUpperLower :
      (0.07756 : ℝ) < Real.sin deltaUpper := by
    have hApprox := (abs_le.mp (Real.sin_bound hDeltaUpperAbs)).1
    rw [abs_of_pos hDeltaUpperPositive] at hApprox
    nlinarith only [hApprox, hDeltaUpperLower,
      hDeltaUpperCubeUpper, hDeltaUpperFourthUpper]
  have hCosDeltaUpperLower :
      (0.99698 : ℝ) < Real.cos deltaUpper := by
    have hApprox := (abs_le.mp (Real.cos_bound hDeltaUpperAbs)).1
    rw [abs_of_pos hDeltaUpperPositive] at hApprox
    nlinarith only [hApprox, hDeltaUpperSqUpper,
      hDeltaUpperFourthUpper]
  have hSqrtSinUpperProduct :
      (1.732 : ℝ) * 0.07756 <
        Real.sqrt 3 * Real.sin deltaUpper :=
    mul_lt_mul hSqrtThreeLower hSinDeltaUpperLower.le
      (by norm_num) (Real.sqrt_nonneg 3)
  have hUpperEndpointSine :
      (0.56515 : ℝ) <
        Real.sin ((34.45 : ℝ) * Real.pi / 180) := by
    have hAngle :
        (34.45 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + deltaUpper := by
      dsimp [deltaUpper]
      ring
    rw [hAngle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only [hCosDeltaUpperLower, hSqrtSinUpperProduct]
  have hLowerAngleNonnegative :
      0 ≤ (34.35 : ℝ) * Real.pi / 180 := by positivity
  have hLowerAngleAcute :
      (34.35 : ℝ) * Real.pi / 180 ≤ Real.pi / 2 := by
    nlinarith only [Real.pi_pos]
  have hUpperAngleNonnegative :
      0 ≤ (34.45 : ℝ) * Real.pi / 180 := by positivity
  have hUpperAngleAcute :
      (34.45 : ℝ) * Real.pi / 180 ≤ Real.pi / 2 := by
    nlinarith only [Real.pi_pos]
  have hAngleLower :
      (34.35 : ℝ) * Real.pi / 180 ≤ setup.braggAngleRadians := by
    by_contra h
    have hAngleStrict :
        setup.braggAngleRadians <
          (34.35 : ℝ) * Real.pi / 180 :=
      lt_of_not_ge h
    have hSinStrict :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ setup.braggAngleRadians by
          nlinarith only [hPhysical.braggAnglePositive, Real.pi_pos])
        hLowerAngleAcute hAngleStrict
    linarith only [hSinStrict, hLowerEndpointSine, hSinThetaLower]
  have hAngleUpper :
      setup.braggAngleRadians <
        (34.45 : ℝ) * Real.pi / 180 := by
    by_contra h
    have hAngleLower :
        (34.45 : ℝ) * Real.pi / 180 ≤ setup.braggAngleRadians :=
      le_of_not_gt h
    have hSinLe :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi / 2) ≤
            (34.45 : ℝ) * Real.pi / 180 by
          nlinarith only [hUpperAngleNonnegative, Real.pi_pos])
        hPhysical.braggAngleAcute.le hAngleLower
    linarith only [hSinLe, hUpperEndpointSine, hSinThetaUpper]
  constructor
  · unfold angleInDegrees
    calc
      (34.35 : ℝ) =
          ((34.35 : ℝ) * Real.pi / 180) * 180 / Real.pi := by
        field_simp [ne_of_gt Real.pi_pos]
      _ ≤ setup.braggAngleRadians * 180 / Real.pi := by
        exact (div_le_div_iff_of_pos_right Real.pi_pos).2
          (mul_le_mul_of_nonneg_right hAngleLower (by norm_num))
  · unfold angleInDegrees
    calc
      setup.braggAngleRadians * 180 / Real.pi <
          ((34.45 : ℝ) * Real.pi / 180) * 180 / Real.pi := by
        exact (div_lt_div_iff_of_pos_right Real.pi_pos).2
          (mul_lt_mul_of_pos_right hAngleUpper (by norm_num))
      _ = (34.45 : ℝ) := by
        field_simp [ne_of_gt Real.pi_pos]

/-!
Blueprint: `thm:physics:phyx_mini_0557:target`.

For the reactor/crystal setup shown in image 557, the selected neutron
wavelength lies near `0.279 nm`, only first-order diffraction is feasible, and
the angle marked `θ` rounds to `34.4°`.  Consequently choice D is the unique
displayed angle matching the physical model.  No premise above contains this
wavelength interval, order conclusion, angular interval, rounded value, or
answer label.
-/
theorem bragg_scattering_angle_is_choice_D
    (setup : ThermalNeutronBraggSetup)
    (hScenario : MatchesThermalNeutronBraggScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedReactorCrystalFigure setup)
    (hReference : UsesStandardNeutronReferenceData setup)
    (hPhysical : HasPhysicalBraggParameters setup)
    (hLaws : SatisfiesThermalNeutronBraggLaws setup) :
    (0.278 < lengthInNanometers setup.scatteredMatterWavelength ∧
        lengthInNanometers setup.scatteredMatterWavelength < 0.280) ∧
      setup.braggOrder = 1 ∧
        (34.35 ≤ angleInDegrees setup.braggAngleRadians ∧
          angleInDegrees setup.braggAngleRadians < 34.45) ∧
        IsUniqueMatchingDisplayedBraggAngle setup .D := by
  have hWavelength :=
    selected_neutron_wavelength_nanometers_in_interval
      setup hScenario hReadouts hReference hPhysical hLaws
  have hOrder :=
    bragg_order_eq_one setup hScenario hReadouts hReference hPhysical hLaws
  have hAngle :=
    bragg_angle_degrees_in_rounding_interval
      setup hScenario hReadouts hReference hPhysical hLaws
  have hRound :
      round (10 * angleInDegrees setup.braggAngleRadians) = 344 := by
    apply round_eq_iff.mpr
    constructor
    · norm_num
      nlinarith only [hAngle.1]
    · norm_num
      nlinarith only [hAngle.2]
  refine ⟨hWavelength, hOrder, hAngle, ?_⟩
  unfold IsUniqueMatchingDisplayedBraggAngle
  constructor
  · unfold MatchesDisplayedBraggAngle RoundsToOneDecimalDegree
    rw [hRound]
    norm_num [AnswerChoice.angleDegrees]
  · intro other hOther
    unfold MatchesDisplayedBraggAngle RoundsToOneDecimalDegree at hOther
    rw [hRound] at hOther
    cases other with
    | A => norm_num [AnswerChoice.angleDegrees] at hOther
    | B => norm_num [AnswerChoice.angleDegrees] at hOther
    | C => norm_num [AnswerChoice.angleDegrees] at hOther
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0557
