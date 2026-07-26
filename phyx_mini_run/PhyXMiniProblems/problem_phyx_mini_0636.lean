import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0636

open Dimension

/-!
# Kinetic energy of a beta particle at the nuclear surface

Cesium-137 beta decays and an emitted beta-minus particle is later observed
with kinetic energy `300 keV`. The supplied figure places the particle at the
surface of a `6.2 fm`-radius nucleus carrying charge `55 e`, gives the beta
particle charge as `-e`, and takes its final electrostatic potential energy to
be zero. Conservation of `K + U`, together with the attractive Coulomb
potential at the surface, determines the larger ejection kinetic energy.

Lengths, signed charges, Coulomb's constant, and energies are dimensionful
quantities. Real numbers occur only at explicit unit-readout boundaries and
in literal figure or answer-choice data. In particular, the requested
ejection kinetic energy is an independent field of the setup and is not fixed
by any data or law premise.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The dimension of Coulomb's constant, equivalently `J m / C²`. -/
def coulombConstantDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in femtometres. -/
def lengthInFemtometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.femtometers length

/-- Read a signed physical charge in coherent-SI coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a dimensionful value of Coulomb's constant in `J m / C²`. -/
def coulombConstantInJouleMetersPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read a signed physical energy in coherent-SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Physlib's positive elementary-charge unit expressed in coulombs. -/
def elementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- Read a signed charge in units of the positive elementary charge. -/
def signedChargeInElementaryCharges (charge : SignedChargeQuantity) : ℝ :=
  signedChargeInCoulombs charge / elementaryChargeInCoulombs

/-- The joule readout of Physlib's dimensionful electron volt. -/
def electronVoltInJoules : ℝ :=
  energyInJoules DimEnergy.electronVolt

/-- One kiloelectronvolt expressed in joules. -/
def kiloElectronVoltInJoules : ℝ :=
  1000 * electronVoltInJoules

/-- One megaelectronvolt expressed in joules. -/
def megaElectronVoltInJoules : ℝ :=
  1000000 * electronVoltInJoules

/-- Read a physical energy in kiloelectronvolts. -/
def energyInKiloElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / kiloElectronVoltInJoules

/-- Read a physical energy in megaelectronvolts. -/
def energyInMegaElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / megaElectronVoltInJoules

/-! ## Physical setup and primary-figure vocabulary -/

/-- The two states labelled `Before` and `After` in the supplied figure. -/
inductive InteractionState where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Nuclear regions occupied by the emitted beta particle in the model. -/
inductive RadialRegion where
  | nuclearSurface
  | asymptoticallyFar
  deriving DecidableEq, Fintype, Repr

/-- The radioactive mode stated in the problem. -/
inductive DecayMode where
  | betaMinus
  | other
  deriving DecidableEq, Repr

/-- Particle species distinguished by this model. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Qualitative direction of the arrows drawn beside the beta particle. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-!
Literal presentation data from image 636. The numerical fields are printed
readouts; their calibration to physical quantities is stated separately.
-/
structure CesiumBetaDecayFigure where
  stateHeading : InteractionState → String
  kineticEnergySymbol : InteractionState → String
  potentialEnergySymbol : InteractionState → String
  betaRegion : InteractionState → RadialRegion
  betaMotionDirection : InteractionState → HorizontalDirection
  cesiumNucleusLabel : String
  radiusLabelFemtometers : ℝ
  nucleusChargeLabelInElementaryCharges : ℝ
  betaChargeLabelInElementaryCharges : ℝ
  finalKineticEnergyLabelKiloElectronVolts : ℝ
  finalPotentialEnergyLabelKiloElectronVolts : ℝ

/-!
Independent physical data for the beta-particle/nucleus interaction. The
before-state kinetic energy is stored as an observable and is constrained
only through the general laws below; it is not defined from `13.1 MeV`.
-/
structure CesiumBetaEjectionSetup where
  isotopeMassNumber : ℕ
  atomicNumber : ℕ
  decayMode : DecayMode
  emittedParticle : ParticleSpecies
  nucleusDiameter : LengthQuantity
  nucleusRadius : LengthQuantity
  surfaceSeparation : LengthQuantity
  nucleusCharge : SignedChargeQuantity
  betaCharge : SignedChargeQuantity
  coulombConstant : CoulombConstantQuantity
  vacuumElectromagneticSystem : Electromagnetism.EMSystem
  particleRegionAt : InteractionState → RadialRegion
  kineticEnergyAt : InteractionState → DimEnergy
  electrostaticPotentialEnergyAt : InteractionState → DimEnergy
  figure : CesiumBetaDecayFigure

/-! ## Scenario, figure evidence, and physical calibrations -/

/-- Cesium-137, atomic number 55, undergoing beta-minus decay. -/
structure MatchesCesium137BetaDecayScenario
    (setup : CesiumBetaEjectionSetup) : Prop where
  isotopeIsCesium137 : setup.isotopeMassNumber = 137
  atomicNumberIs55 : setup.atomicNumber = 55
  decayIsBetaMinus : setup.decayMode = .betaMinus
  emittedParticleIsElectron : setup.emittedParticle = .electron
  statedNucleusDiameterFemtometers :
    lengthInFemtometers setup.nucleusDiameter = 62 / 5
  ejectedAtNuclearSurface :
    setup.particleRegionAt .before = .nuclearSurface
  observedFarFromNucleus :
    setup.particleRegionAt .after = .asymptoticallyFar

/-- All unambiguous symbols, words, arrows, and numbers visible in image 636. -/
structure MatchesSuppliedCesiumBetaFigure
    (setup : CesiumBetaEjectionSetup) : Prop where
  beforeHeading : setup.figure.stateHeading .before = "Before"
  afterHeading : setup.figure.stateHeading .after = "After"
  beforeKineticSymbol : setup.figure.kineticEnergySymbol .before = "K_i"
  afterKineticSymbol : setup.figure.kineticEnergySymbol .after = "K_f"
  beforePotentialSymbol : setup.figure.potentialEnergySymbol .before = "U_i"
  afterPotentialSymbol : setup.figure.potentialEnergySymbol .after = "U_f"
  nucleusLabel : setup.figure.cesiumNucleusLabel = "Cesium nucleus"
  beforeRegion : setup.figure.betaRegion .before = .nuclearSurface
  afterRegion : setup.figure.betaRegion .after = .asymptoticallyFar
  arrowsPointRight : ∀ state,
    setup.figure.betaMotionDirection state = .rightward
  radiusReadout : setup.figure.radiusLabelFemtometers = 31 / 5
  nucleusChargeReadout :
    setup.figure.nucleusChargeLabelInElementaryCharges = 55
  betaChargeReadout :
    setup.figure.betaChargeLabelInElementaryCharges = -1
  finalKineticEnergyReadout :
    setup.figure.finalKineticEnergyLabelKiloElectronVolts = 300
  finalPotentialEnergyReadout :
    setup.figure.finalPotentialEnergyLabelKiloElectronVolts = 0

/-!
Calibration of the literal figure readouts to the independent physical
quantities. Only the final observed energy and the two charges are supplied;
the requested before-state kinetic energy is absent.
-/
structure UsesSuppliedFigureCalibration
    (setup : CesiumBetaEjectionSetup) : Prop where
  physicalRegions : ∀ state,
    setup.particleRegionAt state = setup.figure.betaRegion state
  radiusCalibration :
    lengthInFemtometers setup.nucleusRadius =
      setup.figure.radiusLabelFemtometers
  nucleusChargeCalibration :
    signedChargeInElementaryCharges setup.nucleusCharge =
      setup.figure.nucleusChargeLabelInElementaryCharges
  betaChargeCalibration :
    signedChargeInElementaryCharges setup.betaCharge =
      setup.figure.betaChargeLabelInElementaryCharges
  finalKineticEnergyCalibration :
    energyInKiloElectronVolts (setup.kineticEnergyAt .after) =
      setup.figure.finalKineticEnergyLabelKiloElectronVolts
  finalPotentialEnergyCalibration :
    energyInKiloElectronVolts
        (setup.electrostaticPotentialEnergyAt .after) =
      setup.figure.finalPotentialEnergyLabelKiloElectronVolts

/-- The diameter, radius, and surface separation describe the same nucleus. -/
structure HasNuclearSurfaceGeometry
    (setup : CesiumBetaEjectionSetup) : Prop where
  diameterIsTwiceRadius :
    lengthInMeters setup.nucleusDiameter =
      2 * lengthInMeters setup.nucleusRadius
  surfaceSeparationIsRadius :
    lengthInMeters setup.surfaceSeparation =
      lengthInMeters setup.nucleusRadius

/-- Positivity and sign conditions for the physical parameters. -/
structure HasPhysicalCesiumBetaParameters
    (setup : CesiumBetaEjectionSetup) : Prop where
  elementaryChargePositive : 0 < elementaryChargeInCoulombs
  electronVoltPositive : 0 < electronVoltInJoules
  nucleusRadiusPositive : 0 < lengthInMeters setup.nucleusRadius
  surfaceSeparationPositive : 0 < lengthInMeters setup.surfaceSeparation
  coulombConstantPositive :
    0 < coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant
  kineticEnergiesNonnegative : ∀ state,
    0 ≤ energyInJoules (setup.kineticEnergyAt state)

/-!
The dimensionful Coulomb constant is calibrated to Physlib's electromagnetic
system and to the standard vacuum SI readout. This supplies a physical
constant, not the requested kinetic-energy answer.
-/
structure UsesVacuumCoulombConstant
    (setup : CesiumBetaEjectionSetup) : Prop where
  agreesWithElectromagneticSystem :
    coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant =
      Electromagnetism.EMSystem.coulombConstant
        setup.vacuumElectromagneticSystem
  vacuumSIReadout :
    Electromagnetism.EMSystem.coulombConstant
        setup.vacuumElectromagneticSystem =
      89875517923 / 10

/-! ## Governing electrostatic laws -/

/-!
The beta particle starts one nuclear radius from the centre, so its initial
electrostatic potential energy is the attractive point-charge Coulomb energy.
Mechanical energy `K + U` is conserved between the two displayed states.
Neither relation contains a numerical value for the initial kinetic energy.
-/
structure SatisfiesIdealElectrostaticEjectionLaws
    (setup : CesiumBetaEjectionSetup) : Prop where
  surfaceCoulombPotentialEnergy :
    energyInJoules (setup.electrostaticPotentialEnergyAt .before) =
      coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
          signedChargeInCoulombs setup.nucleusCharge *
          signedChargeInCoulombs setup.betaCharge /
        lengthInMeters setup.surfaceSeparation
  mechanicalEnergyConservation :
    energyInJoules (setup.kineticEnergyAt .before) +
        energyInJoules (setup.electrostaticPotentialEnergyAt .before) =
      energyInJoules (setup.kineticEnergyAt .after) +
        energyInJoules (setup.electrostaticPotentialEnergyAt .after)

/-! ## Derived energy, printed choices, and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Ejection kinetic energy printed beside each answer, in megaelectronvolts. -/
def AnswerChoice.ejectionKineticEnergyInMegaElectronVolts : AnswerChoice → ℝ
  | .A => 127 / 10
  | .B => 131 / 10
  | .C => 134 / 10
  | .D => 138 / 10

/-- Half of the `0.1 MeV` precision displayed by the answer values. -/
def displayedEnergyRoundingToleranceInMegaElectronVolts : ℝ :=
  1 / 20

/-- The physical ejection energy rounds to the value printed for a choice. -/
def MatchesDisplayedEjectionEnergy
    (setup : CesiumBetaEjectionSetup) (choice : AnswerChoice) : Prop :=
  |energyInMegaElectronVolts (setup.kineticEnergyAt .before) -
      choice.ejectionKineticEnergyInMegaElectronVolts| <
    displayedEnergyRoundingToleranceInMegaElectronVolts

/-- Exactly one printed choice matches at the displayed precision. -/
def IsUniqueMatchingDisplayedEjectionEnergy
    (setup : CesiumBetaEjectionSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedEjectionEnergy setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedEjectionEnergy setup other → other = choice

/-- The source dataset's recorded answer, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Conservation of energy and the surface Coulomb law first give the exact
coherent-SI balance, before any numerical constants are substituted.
-/
lemma ejectionKineticEnergy_coulombBalance
    (setup : CesiumBetaEjectionSetup)
    (hCalibration : UsesSuppliedFigureCalibration setup)
    (hFigure : MatchesSuppliedCesiumBetaFigure setup)
    (hLaws : SatisfiesIdealElectrostaticEjectionLaws setup) :
    energyInJoules (setup.kineticEnergyAt .before) =
      energyInJoules (setup.kineticEnergyAt .after) -
        coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant *
            signedChargeInCoulombs setup.nucleusCharge *
            signedChargeInCoulombs setup.betaCharge /
          lengthInMeters setup.surfaceSeparation := by
  have hElectronVolt : 0 < electronVoltInJoules := by
    norm_num [electronVoltInJoules, energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  have hFinalPotentialKeV :=
    hCalibration.finalPotentialEnergyCalibration
  rw [hFigure.finalPotentialEnergyReadout] at hFinalPotentialKeV
  rw [energyInKiloElectronVolts, kiloElectronVoltInJoules] at hFinalPotentialKeV
  have hFinalPotential :
      energyInJoules (setup.electrostaticPotentialEnergyAt .after) = 0 := by
    exact (div_eq_zero_iff.mp hFinalPotentialKeV).resolve_right
      (mul_ne_zero (by norm_num) hElectronVolt.ne')
  have hSurface := hLaws.surfaceCoulombPotentialEnergy
  linarith [hLaws.mechanicalEnergyConservation]

/-!
After inserting the figure charges, radius, and final `300 keV`, the ejection
energy is `0.3 MeV` plus the positive magnitude of the attractive surface
Coulomb potential.
-/
lemma ejectionKineticEnergy_eq_coulombCorrectedFinalEnergy
    (setup : CesiumBetaEjectionSetup)
    (hFigure : MatchesSuppliedCesiumBetaFigure setup)
    (hCalibration : UsesSuppliedFigureCalibration setup)
    (hGeometry : HasNuclearSurfaceGeometry setup)
    (hPhysical : HasPhysicalCesiumBetaParameters setup)
    (hLaws : SatisfiesIdealElectrostaticEjectionLaws setup) :
    energyInMegaElectronVolts (setup.kineticEnergyAt .before) =
      3 / 10 +
        (coulombConstantInJouleMetersPerCoulombSquared
              setup.coulombConstant *
            55 * elementaryChargeInCoulombs ^ 2 /
            lengthInMeters setup.nucleusRadius) /
          megaElectronVoltInJoules := by
  have hFinalKineticKeV := hCalibration.finalKineticEnergyCalibration
  rw [hFigure.finalKineticEnergyReadout] at hFinalKineticKeV
  have hFinalKineticMeV :
      energyInMegaElectronVolts (setup.kineticEnergyAt .after) = 3 / 10 := by
    rw [energyInKiloElectronVolts, kiloElectronVoltInJoules] at hFinalKineticKeV
    rw [energyInMegaElectronVolts, megaElectronVoltInJoules]
    field_simp [ne_of_gt hPhysical.electronVoltPositive] at hFinalKineticKeV ⊢
    nlinarith
  have hNucleusChargeRatio := hCalibration.nucleusChargeCalibration
  rw [hFigure.nucleusChargeReadout] at hNucleusChargeRatio
  have hNucleusCharge :
      signedChargeInCoulombs setup.nucleusCharge =
        55 * elementaryChargeInCoulombs := by
    rw [signedChargeInElementaryCharges] at hNucleusChargeRatio
    field_simp [ne_of_gt hPhysical.elementaryChargePositive] at hNucleusChargeRatio
    linarith
  have hBetaChargeRatio := hCalibration.betaChargeCalibration
  rw [hFigure.betaChargeReadout] at hBetaChargeRatio
  have hBetaCharge :
      signedChargeInCoulombs setup.betaCharge =
        -elementaryChargeInCoulombs := by
    rw [signedChargeInElementaryCharges] at hBetaChargeRatio
    field_simp [ne_of_gt hPhysical.elementaryChargePositive] at hBetaChargeRatio
    linarith
  have hBalance :=
    ejectionKineticEnergy_coulombBalance setup hCalibration hFigure hLaws
  calc
    energyInMegaElectronVolts (setup.kineticEnergyAt .before) =
        energyInMegaElectronVolts (setup.kineticEnergyAt .after) +
          (coulombConstantInJouleMetersPerCoulombSquared
                setup.coulombConstant *
              55 * elementaryChargeInCoulombs ^ 2 /
              lengthInMeters setup.nucleusRadius) /
            megaElectronVoltInJoules := by
      simp only [energyInMegaElectronVolts]
      rw [hBalance, hNucleusCharge, hBetaCharge,
        hGeometry.surfaceSeparationIsRadius]
      ring
    _ = 3 / 10 +
          (coulombConstantInJouleMetersPerCoulombSquared
                setup.coulombConstant *
              55 * elementaryChargeInCoulombs ^ 2 /
              lengthInMeters setup.nucleusRadius) /
            megaElectronVoltInJoules := by
      rw [hFinalKineticMeV]

/-!
The exact surface-Coulomb correction is approximately `12.774 MeV`, so the
ejection energy is approximately `13.074 MeV`. At the displayed precision it
is `13.1 MeV`, uniquely selecting answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0636:target`.
-/
theorem problem_phyx_mini_0636
    (setup : CesiumBetaEjectionSetup)
    (hScenario : MatchesCesium137BetaDecayScenario setup)
    (hFigure : MatchesSuppliedCesiumBetaFigure setup)
    (hCalibration : UsesSuppliedFigureCalibration setup)
    (hGeometry : HasNuclearSurfaceGeometry setup)
    (hPhysical : HasPhysicalCesiumBetaParameters setup)
    (hCoulombConstant : UsesVacuumCoulombConstant setup)
    (hLaws : SatisfiesIdealElectrostaticEjectionLaws setup) :
    energyInMegaElectronVolts (setup.kineticEnergyAt .before) =
        3 / 10 +
          (coulombConstantInJouleMetersPerCoulombSquared
                setup.coulombConstant *
              55 * elementaryChargeInCoulombs ^ 2 /
              lengthInMeters setup.nucleusRadius) /
            megaElectronVoltInJoules ∧
      MatchesDisplayedEjectionEnergy setup .B ∧
      IsUniqueMatchingDisplayedEjectionEnergy setup .B := by
  have hFormula :=
    ejectionKineticEnergy_eq_coulombCorrectedFinalEnergy
      setup hFigure hCalibration hGeometry hPhysical hLaws
  have hCoulomb :
      coulombConstantInJouleMetersPerCoulombSquared setup.coulombConstant =
        89875517923 / 10 :=
    hCoulombConstant.agreesWithElectromagneticSystem.trans
      hCoulombConstant.vacuumSIReadout
  have hElementary :
      elementaryChargeInCoulombs = 1.602176634e-19 := by
    rw [elementaryChargeInCoulombs, ChargeUnit.elementaryCharge,
      ChargeUnit.scale_div_self]
    rfl
  have hMegaElectronVolt :
      megaElectronVoltInJoules = 1.602176634e-13 := by
    norm_num [megaElectronVoltInJoules, electronVoltInJoules, energyInJoules,
      DimEnergy.electronVolt, CarriesDimension.toDimensionful_apply_apply]
  have hLengthConversion (length : LengthQuantity) :
      lengthInMeters length = 1e-15 * lengthInFemtometers length := by
    have hscale := congrArg (fun x => (x.val : ℝ)) (length.2
      ({UnitChoices.SI with length := LengthUnit.femtometers})
        UnitChoices.SI)
    norm_num [lengthInMeters, lengthInFemtometers, lengthReadout,
      UnitChoices.SI, UnitChoices.dimScale, LengthUnit.femtometers,
      LengthUnit.scale, LengthUnit.meters, LengthUnit.div_eq_val]
      at hscale ⊢
    exact hscale
  have hRadiusMeters :
      lengthInMeters setup.nucleusRadius = (31 / 5) * 1e-15 := by
    rw [hLengthConversion, hCalibration.radiusCalibration,
      hFigure.radiusReadout]
    ring
  have hMatchesB : MatchesDisplayedEjectionEnergy setup .B := by
    rw [MatchesDisplayedEjectionEnergy, hFormula, hCoulomb, hElementary,
      hMegaElectronVolt, hRadiusMeters]
    norm_num [AnswerChoice.ejectionKineticEnergyInMegaElectronVolts,
      displayedEnergyRoundingToleranceInMegaElectronVolts]
  have hUniqueB : IsUniqueMatchingDisplayedEjectionEnergy setup .B := by
    refine ⟨hMatchesB, ?_⟩
    intro other hOther
    fin_cases other
    · rw [MatchesDisplayedEjectionEnergy, hFormula, hCoulomb, hElementary,
        hMegaElectronVolt, hRadiusMeters] at hOther
      norm_num [AnswerChoice.ejectionKineticEnergyInMegaElectronVolts,
        displayedEnergyRoundingToleranceInMegaElectronVolts] at hOther
    · rfl
    · rw [MatchesDisplayedEjectionEnergy, hFormula, hCoulomb, hElementary,
        hMegaElectronVolt, hRadiusMeters] at hOther
      norm_num [AnswerChoice.ejectionKineticEnergyInMegaElectronVolts,
        displayedEnergyRoundingToleranceInMegaElectronVolts] at hOther
    · rw [MatchesDisplayedEjectionEnergy, hFormula, hCoulomb, hElementary,
        hMegaElectronVolt, hRadiusMeters] at hOther
      norm_num [AnswerChoice.ejectionKineticEnergyInMegaElectronVolts,
        displayedEnergyRoundingToleranceInMegaElectronVolts] at hOther
  exact ⟨hFormula, hMatchesB, hUniqueB⟩

end PhyXMiniProblems.ProblemPhyXMini0636
