import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0623

open Dimension

/-!
# Surface-atom separation from electron diffraction

A normally incident `100 eV` electron beam scatters from atoms in the surface
layer of a crystalline solid.  The first diffraction maximum is observed at
`24°`.  The primary figure marks the adjacent-atom separation `d`, the
scattering angle `θ`, and the path difference `d sin θ`.

Energy, mass, momentum magnitude, action, wavelength, path difference, and
atom separation are unit-independent dimensionful quantities.  Real numbers
occur only as calibrated unit readouts, angles, and displayed answer values.
In particular, the atom separation is an independent field of the setup; it
is not defined from the recorded answer.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension `mass * length / time` of a momentum magnitude. -/
def momentumDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical momentum magnitude. -/
abbrev MomentumMagnitudeQuantity : Type :=
  Dimensionful (WithDim momentumDimension NNReal)

/-- The dimension `mass * length² / time` of an action. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout used for the four displayed separations. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Coherent-SI energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Electron-volt readout grounded by Physlib's dimensionful calibrated
`DimEnergy.electronVolt`, rather than by treating energy as a bare scalar.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Coherent-SI mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Coherent-SI momentum-magnitude readout in kilogram-metres per second. -/
def momentumInKilogramMetersPerSecond
    (momentum : MomentumMagnitudeQuantity) : ℝ :=
  ((momentum UnitChoices.SI).val : ℝ)

/-- Coherent-SI action readout in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of Physlib's exact vacuum light-speed constant. -/
def speedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- Convert the displayed degree measure of an angle to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Physical roles and primary-figure vocabulary -/

/-- Particle species in the incident beam. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Kind of solid surface struck by the beam. -/
inductive SurfaceKind where
  | crystalline
  | noncrystalline
  deriving DecidableEq, Repr

/-- Direction of incidence relative to the surface. -/
inductive IncidenceGeometry where
  | perpendicularToSurface
  | obliqueToSurface
  deriving DecidableEq, Repr

/-- Beam arrows represented in the primary diagram. -/
inductive FigureBeam where
  | incident
  | leftScattered
  | rightScattered
  deriving DecidableEq, Fintype, Repr

/-- Length labels printed in the primary diagram. -/
inductive FigureLengthLabel where
  | adjacentAtomSeparationD
  | pathDifferenceDSinTheta
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative information transcribed from image `623.png`.  The diagram is
schematic: it supplies labels and incidence/scattering geometry, but no
additional numerical length measurement.
-/
structure SurfaceDiffractionFigure where
  showsAtomsInGrid : Bool
  showsTwoAdjacentSurfaceAtoms : Bool
  showsBeamArrow : FigureBeam → Bool
  incidentArrowIsPerpendicularToSurface : Bool
  scatteredArrowsAreSymmetric : Bool
  showsThetaAtBothScatteringPoints : Bool
  showsLengthLabel : FigureLengthLabel → Bool
  pathDifferenceConstructionIsDashed : Bool

/-!
Independent physical quantities in the experiment.  `pathDifferenceAt` is
the outgoing-ray path difference for an angle measured in degrees, and
`isDiffractionMaximum order angle` records an observed maximum without
defining either the wavelength or atom separation.
-/
structure ElectronSurfaceDiffractionSetup where
  particleSpecies : ParticleSpecies
  surfaceKind : SurfaceKind
  incidenceGeometry : IncidenceGeometry
  interactionRestrictedToSurfaceLayer : Bool
  incidentKineticEnergy : DimEnergy
  electronMass : MassQuantity
  incidentMomentumMagnitude : MomentumMagnitudeQuantity
  ordinaryPlanckAction : ActionQuantity
  matterWavelength : LengthQuantity
  adjacentSurfaceAtomSeparation : LengthQuantity
  pathDifferenceAt : ℝ → LengthQuantity
  isDiffractionMaximum : ℕ → ℝ → Prop
  smallestMaximumAngleDegrees : ℝ
  figure : SurfaceDiffractionFigure

/-! ## Scenario, readouts, primary-image facts, and governing laws -/

/-- Qualitative physical scenario stated in the problem. -/
structure MatchesElectronSurfaceDiffractionScenario
    (setup : ElectronSurfaceDiffractionSetup) : Prop where
  incidentParticlesAreElectrons : setup.particleSpecies = .electron
  targetSurfaceIsCrystalline : setup.surfaceKind = .crystalline
  beamIsNormallyIncident :
    setup.incidenceGeometry = .perpendicularToSurface
  onlySurfaceLayerInteracts :
    setup.interactionRestrictedToSurfaceLayer = true

/-!
The two numerical readouts stated in the prose.  The designation of the
smallest positive maximum as order one is the usual diffraction-order naming
for this normal-incidence setup.  No wavelength or atom-separation value
occurs here.
-/
structure MatchesProblemReadouts
    (setup : ElectronSurfaceDiffractionSetup) : Prop where
  kineticEnergyElectronVolts :
    energyInElectronVolts setup.incidentKineticEnergy = 100
  smallestMaximumAngle : setup.smallestMaximumAngleDegrees = 24
  observedMaximumIsFirstOrder :
    setup.isDiffractionMaximum 1 setup.smallestMaximumAngleDegrees
  smallestAmongPositiveMaximumAngles :
    ∀ order angleDegrees,
      0 < order →
      0 < angleDegrees →
      setup.isDiffractionMaximum order angleDegrees →
      setup.smallestMaximumAngleDegrees ≤ angleDegrees

/-! Facts directly visible in the supplied surface-diffraction diagram. -/
structure MatchesSuppliedSurfaceDiffractionFigure
    (figure : SurfaceDiffractionFigure) : Prop where
  atomicGridShown : figure.showsAtomsInGrid = true
  adjacentSurfacePairShown : figure.showsTwoAdjacentSurfaceAtoms = true
  everyBeamArrowShown : ∀ beam, figure.showsBeamArrow beam = true
  incidentBeamNormalToSurface :
    figure.incidentArrowIsPerpendicularToSurface = true
  symmetricScatteredRays : figure.scatteredArrowsAreSymmetric = true
  thetaShownAtBothAtoms :
    figure.showsThetaAtBothScatteringPoints = true
  bothLengthLabelsShown : ∀ label, figure.showsLengthLabel label = true
  dashedPathDifferenceConstruction :
    figure.pathDifferenceConstructionIsDashed = true

/-!
Standard reference data needed by the exact relativistic de Broglie calculation.
Physlib provides `Constants.ℏ` in joule-seconds, so the ordinary Planck action
has readout `2πℏ`.  Physlib has no electron-mass constant, hence the CODATA
electron mass is a calibrated premise.  The exact light-speed constant is
grounded by `DimSpeed.speedOfLight`.  None of these reference values contains
the requested atom separation.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronSurfaceDiffractionSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.electronMass = 9.1093837139e-31
  ordinaryPlanckActionJouleSeconds :
    actionInJouleSeconds setup.ordinaryPlanckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-- Positivity and angle-range conditions selecting the physical regime. -/
structure HasPhysicalSurfaceDiffractionParameters
    (setup : ElectronSurfaceDiffractionSetup) : Prop where
  positiveKineticEnergy : 0 < energyInJoules setup.incidentKineticEnergy
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  positiveIncidentMomentum :
    0 < momentumInKilogramMetersPerSecond
      setup.incidentMomentumMagnitude
  positivePlanckAction :
    0 < actionInJouleSeconds setup.ordinaryPlanckAction
  positiveVacuumLightSpeed : 0 < speedOfLightInMetersPerSecond
  positiveMatterWavelength : 0 < lengthInMeters setup.matterWavelength
  positiveAtomSeparation :
    0 < lengthInMeters setup.adjacentSurfaceAtomSeparation
  smallestAnglePositive : 0 < setup.smallestMaximumAngleDegrees
  smallestAngleAcute : setup.smallestMaximumAngleDegrees < 90

/-!
The governing relations used by the textbook calculation:

* exact relativistic energy--momentum dispersion gives
  `(K + m c²)² = (p c)² + (m c²)²`;
* de Broglie's law gives `λ p = h`;
* the figure geometry gives the path difference `d sin θ`;
* at an order-`n` maximum, that path difference is `n λ`.

The last two equations hold for every angle/order supplied to them.  They do
not specialize the atom separation, wavelength, or answer label to this
problem's requested result.  In particular, the kinetic-energy law is exact:
the low-energy approximation `p² = 2 m K` is deliberately not assumed as an
equality merely from a regime tag.
-/
structure SatisfiesElectronSurfaceDiffractionLaws
    (setup : ElectronSurfaceDiffractionSetup) : Prop where
  relativisticEnergyMomentumLaw :
    (energyInJoules setup.incidentKineticEnergy +
          massInKilograms setup.electronMass *
            speedOfLightInMetersPerSecond ^ 2) ^ 2 =
      (momentumInKilogramMetersPerSecond
            setup.incidentMomentumMagnitude *
          speedOfLightInMetersPerSecond) ^ 2 +
        (massInKilograms setup.electronMass *
            speedOfLightInMetersPerSecond ^ 2) ^ 2
  deBroglieMatterWaveLaw :
    lengthInMeters setup.matterWavelength *
        momentumInKilogramMetersPerSecond setup.incidentMomentumMagnitude =
      actionInJouleSeconds setup.ordinaryPlanckAction
  pathDifferenceGeometry : ∀ angleDegrees,
    lengthInMeters (setup.pathDifferenceAt angleDegrees) =
      lengthInMeters setup.adjacentSurfaceAtomSeparation *
        Real.sin (degreesToRadians angleDegrees)
  constructiveMaximumCondition : ∀ order angleDegrees,
    setup.isDiffractionMaximum order angleDegrees →
      lengthInMeters (setup.pathDifferenceAt angleDegrees) =
        (order : ℝ) * lengthInMeters setup.matterWavelength

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed atom-separation choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Separation in nanometres printed beside each answer label. -/
def displayedSeparationInNanometers : AnswerChoice → ℝ
  | .A => 0.20
  | .B => 0.25
  | .C => 0.30
  | .D => 0.35

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a separation printed to two decimal places in nanometres. -/
def RoundsToHundredthNanometer (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 200

/-- A displayed choice agrees with the atom separation to the shown precision. -/
def MatchesDisplayedSeparation
    (setup : ElectronSurfaceDiffractionSetup)
    (choice : AnswerChoice) : Prop :=
  RoundsToHundredthNanometer
    (lengthInNanometers setup.adjacentSurfaceAtomSeparation)
    (displayedSeparationInNanometers choice)

/-- A choice is the unique displayed separation matching the modeled result. -/
def IsUniqueMatchingDisplayedSeparation
    (setup : ElectronSurfaceDiffractionSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedSeparation setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedSeparation setup other → other = choice

/-!
The exact relativistic dispersion and de Broglie laws determine the electron
matter wavelength without using any diffraction-spacing conclusion.  The
term `(K / c)²` is retained, so this is not the globalized nonrelativistic
approximation rejected by the formalization review gate.
-/
lemma matterWavelength_from_relativisticEnergy
    (setup : ElectronSurfaceDiffractionSetup)
    (h_physical : HasPhysicalSurfaceDiffractionParameters setup)
    (h_laws : SatisfiesElectronSurfaceDiffractionLaws setup) :
    lengthInMeters setup.matterWavelength =
      actionInJouleSeconds setup.ordinaryPlanckAction /
        Real.sqrt
          (2 * massInKilograms setup.electronMass *
              energyInJoules setup.incidentKineticEnergy +
            (energyInJoules setup.incidentKineticEnergy /
                speedOfLightInMetersPerSecond) ^ 2) := by
  have hc_ne : speedOfLightInMetersPerSecond ≠ 0 :=
    ne_of_gt h_physical.positiveVacuumLightSpeed
  have hp_sq :
      momentumInKilogramMetersPerSecond
            setup.incidentMomentumMagnitude ^ 2 =
        2 * massInKilograms setup.electronMass *
            energyInJoules setup.incidentKineticEnergy +
          (energyInJoules setup.incidentKineticEnergy /
              speedOfLightInMetersPerSecond) ^ 2 := by
    field_simp [hc_ne]
    nlinarith only [h_laws.relativisticEnergyMomentumLaw]
  have hradicand_pos :
      0 <
        2 * massInKilograms setup.electronMass *
            energyInJoules setup.incidentKineticEnergy +
          (energyInJoules setup.incidentKineticEnergy /
              speedOfLightInMetersPerSecond) ^ 2 := by
    rw [← hp_sq]
    nlinarith only [h_physical.positiveIncidentMomentum]
  have hsqrt_sq :
      Real.sqrt
            (2 * massInKilograms setup.electronMass *
                energyInJoules setup.incidentKineticEnergy +
              (energyInJoules setup.incidentKineticEnergy /
                  speedOfLightInMetersPerSecond) ^ 2) ^ 2 =
        2 * massInKilograms setup.electronMass *
            energyInJoules setup.incidentKineticEnergy +
          (energyInJoules setup.incidentKineticEnergy /
              speedOfLightInMetersPerSecond) ^ 2 :=
    Real.sq_sqrt hradicand_pos.le
  have hp_eq_sqrt :
      momentumInKilogramMetersPerSecond setup.incidentMomentumMagnitude =
        Real.sqrt
          (2 * massInKilograms setup.electronMass *
              energyInJoules setup.incidentKineticEnergy +
            (energyInJoules setup.incidentKineticEnergy /
                speedOfLightInMetersPerSecond) ^ 2) := by
    nlinarith only [hp_sq, hsqrt_sq,
      h_physical.positiveIncidentMomentum, Real.sqrt_nonneg
        (2 * massInKilograms setup.electronMass *
            energyInJoules setup.incidentKineticEnergy +
          (energyInJoules setup.incidentKineticEnergy /
              speedOfLightInMetersPerSecond) ^ 2)]
  rw [← hp_eq_sqrt]
  exact
    (eq_div_iff (ne_of_gt h_physical.positiveIncidentMomentum)).2
      h_laws.deBroglieMatterWaveLaw

/-!
At the observed first-order maximum, `d sin θ = λ`; solving this general
relation for `d` gives the exact spacing formula used before rounding.
-/
lemma atomSeparation_from_firstMaximum
    (setup : ElectronSurfaceDiffractionSetup)
    (h_physical : HasPhysicalSurfaceDiffractionParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_laws : SatisfiesElectronSurfaceDiffractionLaws setup) :
    lengthInNanometers setup.adjacentSurfaceAtomSeparation =
      lengthInNanometers setup.matterWavelength /
        Real.sin (degreesToRadians 24) := by
  have length_nm_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    have h := congrArg
      (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.nanometers})
    norm_num [lengthInNanometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, NNReal.smul_def] at h ⊢
    exact h
  have hsin_pos : 0 < Real.sin (degreesToRadians 24) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [degreesToRadians]
      positivity
    · rw [degreesToRadians]
      nlinarith only [Real.pi_pos]
  have hgeometry :=
    h_laws.pathDifferenceGeometry setup.smallestMaximumAngleDegrees
  have hmaximum :=
    h_laws.constructiveMaximumCondition 1
      setup.smallestMaximumAngleDegrees
      h_readouts.observedMaximumIsFirstOrder
  rw [h_readouts.smallestMaximumAngle] at hgeometry hmaximum
  norm_num at hmaximum
  have hmeters :
      lengthInMeters setup.adjacentSurfaceAtomSeparation *
          Real.sin (degreesToRadians 24) =
        lengthInMeters setup.matterWavelength := by
    nlinarith only [hgeometry, hmaximum]
  rw [length_nm_eq, length_nm_eq]
  apply (eq_div_iff (ne_of_gt hsin_pos)).2
  nlinarith only [hmeters]

/-!
For a `100 eV` electron, the exact relativistic dispersion relation and de
Broglie's law give a wavelength of about `0.123 nm`; the first-order maximum
condition at `24°` then gives an adjacent surface-atom separation of about
`0.302 nm`.  To the two decimal places shown by the choices, this is `0.30 nm`,
uniquely selecting choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0623:target`.  The
rounded separation and choice C appear only in this conclusion-side section,
not in the scenario, readout, figure, reference-data, positivity, or governing
law premises.
-/
theorem problem_phyx_mini_0623
    (setup : ElectronSurfaceDiffractionSetup)
    (h_scenario : MatchesElectronSurfaceDiffractionScenario setup)
    (h_physical : HasPhysicalSurfaceDiffractionParameters setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedSurfaceDiffractionFigure setup.figure)
    (h_reference : UsesStandardElectronReferenceData setup)
    (h_laws : SatisfiesElectronSurfaceDiffractionLaws setup) :
    lengthInMeters setup.matterWavelength =
        actionInJouleSeconds setup.ordinaryPlanckAction /
          Real.sqrt
            (2 * massInKilograms setup.electronMass *
                energyInJoules setup.incidentKineticEnergy +
              (energyInJoules setup.incidentKineticEnergy /
                  speedOfLightInMetersPerSecond) ^ 2) ∧
      lengthInNanometers setup.adjacentSurfaceAtomSeparation =
        lengthInNanometers setup.matterWavelength /
          Real.sin (degreesToRadians 24) ∧
      RoundsToHundredthNanometer
        (lengthInNanometers setup.adjacentSurfaceAtomSeparation)
        (displayedSeparationInNanometers .C) ∧
      IsUniqueMatchingDisplayedSeparation setup recordedDatasetAnswer := by
  have hWavelength :=
    matterWavelength_from_relativisticEnergy setup h_physical h_laws
  have hSeparation :=
    atomSeparation_from_firstMaximum setup h_physical h_readouts h_laws
  have length_nm_eq (length : LengthQuantity) :
      lengthInNanometers length = 1000000000 * lengthInMeters length := by
    have h := congrArg
      (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.nanometers})
    norm_num [lengthInNanometers, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, NNReal.smul_def] at h ⊢
    exact h
  have hElectronVolt :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    simp [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hEnergy :
      energyInJoules setup.incidentKineticEnergy =
        100 * 1.602176634e-19 := by
    have h := h_readouts.kineticEnergyElectronVolts
    rw [energyInElectronVolts, hElectronVolt] at h
    norm_num at h ⊢
    nlinarith
  have hSpeedOfLight :
      speedOfLightInMetersPerSecond = 299792458 := by
    simp [speedOfLightInMetersPerSecond]
  let q : ℝ :=
    momentumInKilogramMetersPerSecond setup.incidentMomentumMagnitude *
      10 ^ 24
  have hq_pos : 0 < q := by
    dsimp [q]
    exact mul_pos h_physical.positiveIncidentMomentum (by norm_num)
  have hMomentumLaw := h_laws.relativisticEnergyMomentumLaw
  rw [hEnergy, h_reference.electronMassKilograms, hSpeedOfLight] at hMomentumLaw
  have hq_lower : (5.4 : ℝ) < q := by
    dsimp [q]
    nlinarith only [hMomentumLaw, h_physical.positiveIncidentMomentum]
  have hq_upper : q < (5.405 : ℝ) := by
    dsimp [q]
    nlinarith only [hMomentumLaw, h_physical.positiveIncidentMomentum]
  have hPlanckAction :
      actionInJouleSeconds setup.ordinaryPlanckAction =
        2 * Real.pi * 1.054571817e-34 := by
    simpa [Constants.ℏ] using
      h_reference.ordinaryPlanckActionJouleSeconds
  have hScaledDeBroglie :
      lengthInNanometers setup.matterWavelength * q =
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    calc
      lengthInNanometers setup.matterWavelength * q =
          (1000000000 * lengthInMeters setup.matterWavelength) *
            (momentumInKilogramMetersPerSecond
                setup.incidentMomentumMagnitude * 10 ^ 24) := by
        rw [length_nm_eq]
      _ = (lengthInMeters setup.matterWavelength *
              momentumInKilogramMetersPerSecond
                setup.incidentMomentumMagnitude) * 10 ^ 33 := by
        ring
      _ = actionInJouleSeconds setup.ordinaryPlanckAction * 10 ^ 33 := by
        rw [h_laws.deBroglieMatterWaveLaw]
      _ = (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
        rw [hPlanckAction]
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt3_lower : (1.732 : ℝ) < Real.sqrt 3 := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg]
  have hsqrt3_upper : Real.sqrt 3 < (1.733 : ℝ) := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg]
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrt5_lower : (2.236 : ℝ) < Real.sqrt 5 := by
    nlinarith only [hsqrt5_sq, hsqrt5_nonneg]
  have hsqrt5_upper : Real.sqrt 5 < (2.237 : ℝ) := by
    nlinarith only [hsqrt5_sq, hsqrt5_nonneg]
  have hsin5_pos : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith only [Real.pi_pos])
  have hsin5_sq :
      Real.sin (Real.pi / 5) ^ 2 +
          ((1 + Real.sqrt 5) / 4) ^ 2 = 1 := by
    simpa using Real.sin_sq_add_cos_sq (Real.pi / 5)
  have hsin5_lower : (0.587 : ℝ) < Real.sin (Real.pi / 5) := by
    nlinarith only [hsin5_sq, hsqrt5_sq, hsin5_pos,
      hsqrt5_nonneg, hsqrt5_lower, hsqrt5_upper]
  have hsin5_upper : Real.sin (Real.pi / 5) < (0.589 : ℝ) := by
    nlinarith only [hsin5_sq, hsqrt5_sq, hsin5_pos,
      hsqrt5_nonneg, hsqrt5_lower, hsqrt5_upper]
  have hprod_lower :
      (1.732 : ℝ) * (1 + 2.236) <
        Real.sqrt 3 * (1 + Real.sqrt 5) := by
    exact mul_lt_mul hsqrt3_lower (by linarith)
      (by norm_num) (by positivity)
  have hprod_upper :
      Real.sqrt 3 * (1 + Real.sqrt 5) <
        (1.733 : ℝ) * (1 + 2.237) := by
    exact mul_lt_mul hsqrt3_upper (by linarith)
      (by positivity) (by norm_num)
  have hangle :
      degreesToRadians 24 = Real.pi / 3 - Real.pi / 5 := by
    rw [degreesToRadians]
    ring
  have hsin_bounds :
      (0.405 : ℝ) < Real.sin (degreesToRadians 24) ∧
        Real.sin (degreesToRadians 24) < 0.408 := by
    rw [hangle, Real.sin_sub, Real.sin_pi_div_three,
      Real.cos_pi_div_five, Real.cos_pi_div_three]
    constructor <;>
      nlinarith only [hprod_lower, hprod_upper,
        hsin5_lower, hsin5_upper]
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt2_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hsqrt2_sq, hsqrt2_nonneg]
  have hsqrt2_upper : Real.sqrt 2 < (1.4143 : ℝ) := by
    nlinarith only [hsqrt2_sq, hsqrt2_nonneg]
  let u : ℝ := Real.sqrt (2 + Real.sqrt 2)
  have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg _
  have hu_sq : u ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hu_lower : (1.8477 : ℝ) < u := by
    nlinarith only [hu_sq, hu_nonneg, hsqrt2_lower]
  have hu_upper : u < (1.8479 : ℝ) := by
    nlinarith only [hu_sq, hu_nonneg, hsqrt2_upper]
  let v : ℝ := Real.sqrt (2 - u)
  have hv_arg : 0 ≤ 2 - u := by
    nlinarith only [hu_upper]
  have hv_nonneg : 0 ≤ v := Real.sqrt_nonneg _
  have hv_sq : v ^ 2 = 2 - u := Real.sq_sqrt hv_arg
  have hv_lower : (0.39 : ℝ) < v := by
    nlinarith only [hv_sq, hv_nonneg, hu_upper]
  have hv_upper : v < (0.3904 : ℝ) := by
    nlinarith only [hv_sq, hv_nonneg, hu_lower]
  have hsin16_lower : (0.195 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    change (0.195 : ℝ) < v / 2
    linarith only [hv_lower]
  have hsin16_upper : Real.sin (Real.pi / 16) < (0.1952 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    change v / 2 < (0.1952 : ℝ)
    linarith only [hv_upper]
  have sin_lt_local {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx_one | hx_one
    · exact (Real.sin_le_one x).trans_lt hx_one
    have hx_abs : |x| = x := abs_of_nonneg hx.le
    have h_bound :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx_abs]))
    rw [sub_le_iff_le_add', hx_abs] at h_bound
    apply h_bound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos,
      div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp
  have hpi_lower : (3.12 : ℝ) < Real.pi := by
    have h :=
      sin_lt_local (show 0 < Real.pi / 16 by positivity)
    nlinarith only [h, hsin16_lower]
  have hpi_upper : Real.pi < (3.16 : ℝ) := by
    by_contra hnot
    have hpi_lower' : (3.16 : ℝ) ≤ Real.pi := le_of_not_gt hnot
    let x : ℝ := Real.pi / 16
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hx_lower : (0.1975 : ℝ) ≤ x := by
      dsimp [x]
      nlinarith only [hpi_lower']
    have hx_upper : x ≤ (1 : ℝ) / 4 := by
      dsimp [x]
      nlinarith only [Real.pi_le_four]
    have hx_abs : |x| = x := abs_of_pos hx_pos
    have hbound := neg_le_of_abs_le
      (Real.sin_bound (x := x)
        (by rw [hx_abs]; linarith only [hx_upper]))
    rw [hx_abs] at hbound
    have hx3 : x ^ 3 ≤ x * ((1 : ℝ) / 4) ^ 2 := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ ≤ x * ((1 : ℝ) / 4) ^ 2 := by
          gcongr
    have hx4 : x ^ 4 ≤ x * ((1 : ℝ) / 4) ^ 3 := by
      calc
        x ^ 4 = x * x ^ 3 := by ring
        _ ≤ x * ((1 : ℝ) / 4) ^ 3 := by
          gcongr
    have hsin_lower : (0.1952 : ℝ) < Real.sin x := by
      nlinarith only [hbound, hx_lower, hx3, hx4]
    dsimp [x] at hsin_lower
    linarith only [hsin_lower, hsin16_upper]
  have hsin_pos : 0 < Real.sin (degreesToRadians 24) :=
    lt_trans (by norm_num) hsin_bounds.1
  have hScaledSpacing :
      lengthInNanometers setup.adjacentSurfaceAtomSeparation *
            Real.sin (degreesToRadians 24) * q =
        (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 := by
    calc
      lengthInNanometers setup.adjacentSurfaceAtomSeparation *
            Real.sin (degreesToRadians 24) * q =
          (lengthInNanometers setup.matterWavelength /
              Real.sin (degreesToRadians 24)) *
            Real.sin (degreesToRadians 24) * q := by
        rw [hSeparation]
      _ = lengthInNanometers setup.matterWavelength * q := by
        field_simp [ne_of_gt hsin_pos]
      _ = (2 * Real.pi * 1.054571817e-34) * 10 ^ 33 :=
        hScaledDeBroglie
  have hd_pos :
      0 < lengthInNanometers setup.adjacentSurfaceAtomSeparation := by
    rw [length_nm_eq]
    exact mul_pos (by norm_num) h_physical.positiveAtomSeparation
  have hd_bounds :
      (0.295 : ℝ) <
          lengthInNanometers setup.adjacentSurfaceAtomSeparation ∧
        lengthInNanometers setup.adjacentSurfaceAtomSeparation <
          0.305 := by
    constructor
    · by_contra hnot
      have hd_upper :
          lengthInNanometers setup.adjacentSurfaceAtomSeparation ≤
            (0.295 : ℝ) :=
        le_of_not_gt hnot
      have hds_upper :
          lengthInNanometers setup.adjacentSurfaceAtomSeparation *
              Real.sin (degreesToRadians 24) ≤
            (0.295 : ℝ) * 0.408 := by
        exact mul_le_mul hd_upper hsin_bounds.2.le hsin_pos.le
          (by norm_num)
      have hproduct_upper :
          lengthInNanometers setup.adjacentSurfaceAtomSeparation *
                Real.sin (degreesToRadians 24) * q <
            (0.295 : ℝ) * 0.408 * 5.405 :=
        (mul_le_mul_of_nonneg_right hds_upper hq_pos.le).trans_lt
          (mul_lt_mul_of_pos_left hq_upper (by norm_num))
      rw [hScaledSpacing] at hproduct_upper
      norm_num at hproduct_upper ⊢
      nlinarith only [hproduct_upper, hpi_lower]
    · by_contra hnot
      have hd_lower :
          (0.305 : ℝ) ≤
            lengthInNanometers setup.adjacentSurfaceAtomSeparation :=
        le_of_not_gt hnot
      have hds_lower :
          (0.305 : ℝ) * 0.405 ≤
            lengthInNanometers setup.adjacentSurfaceAtomSeparation *
              Real.sin (degreesToRadians 24) := by
        exact mul_le_mul hd_lower hsin_bounds.1.le
          (by norm_num) hd_pos.le
      have hproduct_lower :
          (0.305 : ℝ) * 0.405 * 5.4 <
            lengthInNanometers setup.adjacentSurfaceAtomSeparation *
                Real.sin (degreesToRadians 24) * q :=
        (mul_lt_mul_of_pos_left hq_lower (by norm_num)).trans_le
          (mul_le_mul_of_nonneg_right hds_lower hq_pos.le)
      rw [hScaledSpacing] at hproduct_lower
      norm_num at hproduct_lower ⊢
      nlinarith only [hproduct_lower, hpi_upper]
  have hRoundsC :
      RoundsToHundredthNanometer
        (lengthInNanometers setup.adjacentSurfaceAtomSeparation)
        (displayedSeparationInNanometers .C) := by
    rw [RoundsToHundredthNanometer, displayedSeparationInNanometers,
      abs_lt]
    norm_num
    constructor <;> linarith only [hd_bounds.1, hd_bounds.2]
  have hUnique :
      IsUniqueMatchingDisplayedSeparation setup recordedDatasetAnswer := by
    rw [IsUniqueMatchingDisplayedSeparation, recordedDatasetAnswer]
    refine ⟨hRoundsC, ?_⟩
    intro other hother
    cases other with
    | A =>
        rw [MatchesDisplayedSeparation, RoundsToHundredthNanometer,
          displayedSeparationInNanometers, abs_lt] at hother
        norm_num at hother
        exfalso
        linarith only [hd_bounds.1, hother.2]
    | B =>
        rw [MatchesDisplayedSeparation, RoundsToHundredthNanometer,
          displayedSeparationInNanometers, abs_lt] at hother
        norm_num at hother
        exfalso
        linarith only [hd_bounds.1, hother.2]
    | C => rfl
    | D =>
        rw [MatchesDisplayedSeparation, RoundsToHundredthNanometer,
          displayedSeparationInNanometers, abs_lt] at hother
        norm_num at hother
        exfalso
        linarith only [hd_bounds.2, hother.1]
  exact ⟨hWavelength, hSeparation, hRoundsC, hUnique⟩

end PhyXMiniProblems.ProblemPhyXMini0623
