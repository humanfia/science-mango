import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Fusion yield of a deuterium stage

An outer uranium-235 or plutonium-239 fission trigger drives an imploding,
compressive shock into an inner deuterium region.  Thirty percent of a
`500 kg` deuterium load undergoes the five-deuteron fusion channel

`5 ²H → ³He + ⁴He + ¹H + 2 n`.

The isotope superscripts `3`, `4`, and `1` identify the product nuclides; the
corresponding product multiplicities are one.  This is the baryon-conserving
reading used by the recorded energy-yield calculation.

Masses, speeds, and energies below are unit-independent Physlib quantities.
Real numbers occur only as named-unit readouts, dimensionless fractions and
counts, or displayed megaton ratings.

Assumption/target boundary:

* `MatchesFusionBombProblemData` contains the supplied `500 kg`, `30%`, trigger,
  shock-wave, and reaction-channel data.
* `MatchesPrimaryBombFigure` contains only labels, nesting, and colors visible
  in the primary raster.
* `MatchesReferenceFusionData` contains the tabulated inputs needed for the
  textbook calculation: deuterium mass, reaction mass defect, the working
  speed-of-light value, and the TNT energy conversion.
* `SatisfiesFusionYieldLaws` contains general mass-defect, `E = Δm c²`, event
  count, total-energy, and rating relations.
* There are no previous-part results.
* The requested `8.65 megatons` and answer C occur only in the conclusion and
  the displayed-answer table, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0573

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Kilogram readout of a physical mass in coherent SI units. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy, grounded by Physlib's joule. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Metre-per-second readout of a physical speed in coherent SI units. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Physlib's exact vacuum speed of light, read in metres per second. -/
def exactSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-- The exact SI mass represented by one unified atomic mass unit. -/
def atomicMassUnitInKilograms : ℝ := 1.66053906660e-27

/-- Atomic-mass-unit readout of a physical mass. -/
def massInAtomicMassUnits (mass : MassQuantity) : ℝ :=
  massInKilograms mass / atomicMassUnitInKilograms

/-! ## Nuclear species and reaction stoichiometry -/

/-- Nuclear species named by the reaction, prose, or primary figure. -/
inductive NuclearSpecies where
  | deuterium
  | helium3
  | helium4
  | protium
  | neutron
  | uranium235
  | plutonium239
  deriving DecidableEq, Fintype, Repr

/-- Proton number of each named isotope or free neutron. -/
def NuclearSpecies.protonNumber : NuclearSpecies → ℕ
  | .deuterium => 1
  | .helium3 => 2
  | .helium4 => 2
  | .protium => 1
  | .neutron => 0
  | .uranium235 => 92
  | .plutonium239 => 94

/-- Nucleon (mass) number of each named isotope or free neutron. -/
def NuclearSpecies.massNumber : NuclearSpecies → ℕ
  | .deuterium => 2
  | .helium3 => 3
  | .helium4 => 4
  | .protium => 1
  | .neutron => 1
  | .uranium235 => 235
  | .plutonium239 => 239

/-- Stoichiometric multiplicities on the two sides of a nuclear reaction. -/
structure NuclearReaction where
  reactantCount : NuclearSpecies → ℕ
  productCount : NuclearSpecies → ℕ

/-- The five-deuteron fusion channel stated in the problem. -/
def fiveDeuteriumFusionReaction : NuclearReaction where
  reactantCount
    | .deuterium => 5
    | _ => 0
  productCount
    | .helium3 => 1
    | .helium4 => 1
    | .protium => 1
    | .neutron => 2
    | _ => 0

/-! ## Device and primary-figure vocabulary -/

/-- The two nested regions drawn in the primary image. -/
inductive BombRegion where
  | innerFusionFuel
  | outerFissionTrigger
  deriving DecidableEq, Fintype, Repr

/-- The two blue shades used to distinguish the nested circular regions. -/
inductive CircleShade where
  | mediumBlue
  | lightBlue
  deriving DecidableEq, Repr

/-- The physical role played by the trigger according to the prose. -/
inductive TriggerMechanism where
  | implodingCompressiveShockWave
  deriving DecidableEq, Repr

/-!
Qualitative information transcribed from the primary raster.  The image gives
no calibrated radius or length, so its geometry is categorical rather than a
scalar measurement.
-/
structure EarlyFusionBombFigure where
  regionShown : BombRegion → Bool
  regionsAreConcentricCircles : Bool
  innerRegionIsInsideOuterRegion : Bool
  regionShade : BombRegion → CircleShade
  innerDeuteriumLabelShown : Bool
  outerUranium235LabelShown : Bool
  outerPlutonium239LabelShown : Bool
  outerLabelUsesOr : Bool
  eachLabelHasLeaderDotAndLine : Bool

/-! ## Independent setup quantities -/

/-!
All physical quantities needed by the yield calculation are independent
fields.  In particular, the fusion rating is not defined to be an answer
choice or a numerical constant.
-/
structure DeuteriumFusionBombSetup where
  totalDeuteriumMass : MassQuantity
  reactingFraction : ℝ
  speciesRestMass : NuclearSpecies → MassQuantity
  reaction : NuclearReaction
  reactionMassDefect : MassQuantity
  workingSpeedOfLight : SpeedQuantity
  reactedDeuteriumMass : MassQuantity
  reactionEventCount : ℝ
  energyReleasedPerEvent : DimEnergy
  totalFusionEnergy : DimEnergy
  energyOfOneMegatonTNT : DimEnergy
  fusionRatingMegatonsTNT : ℝ
  triggerFuel : NuclearSpecies
  triggerMechanism : TriggerMechanism
  figure : EarlyFusionBombFigure

/-! ## Problem data, primary-image readouts, and reference data -/

/-- Numerical and categorical data explicitly supplied by the problem text. -/
structure MatchesFusionBombProblemData
    (setup : DeuteriumFusionBombSetup) : Prop where
  totalDeuteriumMassKilograms :
    massInKilograms setup.totalDeuteriumMass = 500
  thirtyPercentUndergoesFusion : setup.reactingFraction = 3 / 10
  statedFusionChannel : setup.reaction = fiveDeuteriumFusionReaction
  triggerIsUranium235OrPlutonium239 :
    setup.triggerFuel = .uranium235 ∨ setup.triggerFuel = .plutonium239
  triggerDrivesImplodingCompressiveShock :
    setup.triggerMechanism = .implodingCompressiveShockWave

/-- Labels, colors, and nesting read directly from the supplied raster. -/
structure MatchesPrimaryBombFigure
    (setup : DeuteriumFusionBombSetup) : Prop where
  bothRegionsShown : ∀ region, setup.figure.regionShown region = true
  concentricCircularRegions : setup.figure.regionsAreConcentricCircles = true
  fusionFuelInsideTrigger : setup.figure.innerRegionIsInsideOuterRegion = true
  innerRegionMediumBlue :
    setup.figure.regionShade .innerFusionFuel = .mediumBlue
  outerRegionLightBlue :
    setup.figure.regionShade .outerFissionTrigger = .lightBlue
  innerLabelIsDeuterium : setup.figure.innerDeuteriumLabelShown = true
  outerLabelIncludesUranium235 : setup.figure.outerUranium235LabelShown = true
  outerLabelIncludesPlutonium239 : setup.figure.outerPlutonium239LabelShown = true
  outerAlternativesJoinedByOr : setup.figure.outerLabelUsesOr = true
  bothLabelsHaveLeaders : setup.figure.eachLabelHasLeaderDotAndLine = true

/-!
Reference values used by the recorded textbook calculation.  The reaction
mass defect `0.027 u` is a nuclear-data input, not the requested bomb rating.
The working value `3.00 × 10^8 m/s` records the precision used in that
calculation; Physlib's exact `DimSpeed.speedOfLight` remains available.
-/
structure MatchesReferenceFusionData
    (setup : DeuteriumFusionBombSetup) : Prop where
  deuteriumNucleusMassAtomicUnits :
    massInAtomicMassUnits (setup.speciesRestMass .deuterium) = 2014 / 1000
  reactionMassDefectAtomicUnits :
    massInAtomicMassUnits setup.reactionMassDefect = 27 / 1000
  workingSpeedOfLightMetersPerSecond :
    speedInMetersPerSecond setup.workingSpeedOfLight = 300_000_000
  workingSpeedApproximatesExactValue :
    |speedInMetersPerSecond setup.workingSpeedOfLight -
        exactSpeedOfLightInMetersPerSecond| ≤ 300_000
  oneMegatonTNTInJoules :
    energyInJoules setup.energyOfOneMegatonTNT = 4_184_000_000_000_000

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalFusionParameters
    (setup : DeuteriumFusionBombSetup) : Prop where
  totalMassPositive : 0 < massInKilograms setup.totalDeuteriumMass
  reactingFractionPositive : 0 < setup.reactingFraction
  reactingFractionAtMostOne : setup.reactingFraction ≤ 1
  everySpeciesMassPositive :
    ∀ species, 0 < massInKilograms (setup.speciesRestMass species)
  massDefectPositive : 0 < massInKilograms setup.reactionMassDefect
  workingSpeedPositive : 0 < speedInMetersPerSecond setup.workingSpeedOfLight
  eventCountNonnegative : 0 ≤ setup.reactionEventCount
  energyPerEventPositive : 0 < energyInJoules setup.energyReleasedPerEvent
  totalFusionEnergyPositive : 0 < energyInJoules setup.totalFusionEnergy
  megatonEnergyPositive : 0 < energyInJoules setup.energyOfOneMegatonTNT

/-- Total rest mass on the reactant side of a channel, in kilograms. -/
def reactantRestMassInKilograms
    (setup : DeuteriumFusionBombSetup) (reaction : NuclearReaction) : ℝ :=
  ∑ species : NuclearSpecies,
    (reaction.reactantCount species : ℝ) *
      massInKilograms (setup.speciesRestMass species)

/-- Total rest mass on the product side of a channel, in kilograms. -/
def productRestMassInKilograms
    (setup : DeuteriumFusionBombSetup) (reaction : NuclearReaction) : ℝ :=
  ∑ species : NuclearSpecies,
    (reaction.productCount species : ℝ) *
      massInKilograms (setup.speciesRestMass species)

/-!
Governing yield relations for the independently stored quantities:

* reacted mass is the stated fraction of the initial fuel mass;
* reaction mass defect is reactant rest mass minus product rest mass;
* each event releases `Δm c²`;
* event count is reacted mass divided by rest mass consumed per event;
* total energy is event count times energy per event; and
* megaton rating is total energy divided by one megaton of TNT.

No field assigns the requested rating or any displayed answer value.
-/
structure SatisfiesFusionYieldLaws
    (setup : DeuteriumFusionBombSetup) : Prop where
  reactedMassFromFraction :
    massInKilograms setup.reactedDeuteriumMass =
      setup.reactingFraction * massInKilograms setup.totalDeuteriumMass
  reactionMassDefectFromRestMasses :
    massInKilograms setup.reactionMassDefect =
      reactantRestMassInKilograms setup setup.reaction -
        productRestMassInKilograms setup setup.reaction
  massEnergyEquivalencePerEvent :
    energyInJoules setup.energyReleasedPerEvent =
      massInKilograms setup.reactionMassDefect *
        speedInMetersPerSecond setup.workingSpeedOfLight ^ 2
  eventCountFromReactedFuel :
    setup.reactionEventCount =
      massInKilograms setup.reactedDeuteriumMass /
        reactantRestMassInKilograms setup setup.reaction
  totalEnergyFromAllEvents :
    energyInJoules setup.totalFusionEnergy =
      setup.reactionEventCount * energyInJoules setup.energyReleasedPerEvent
  megatonRatingFromEnergy :
    setup.fusionRatingMegatonsTNT =
      energyInJoules setup.totalFusionEnergy /
        energyInJoules setup.energyOfOneMegatonTNT

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate fusion ratings. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Megatons-of-TNT value printed beside each answer label. -/
def AnswerChoice.ratingMegatonsTNT : AnswerChoice → ℝ
  | .A => 621 / 100
  | .B => 129 / 10
  | .C => 865 / 100
  | .D => 53 / 10

/-- Dataset metadata records answer C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a rating displayed to two decimal places: the calculated value
is within half a unit in the last displayed decimal place.
-/
def MatchesDisplayedRating
    (ratingMegatonsTNT : ℝ) (choice : AnswerChoice) : Prop :=
  |ratingMegatonsTNT - choice.ratingMegatonsTNT| ≤ 1 / 200

/-!
The supplied values first give the exact textbook calculation

`((0.30 * 500) / (5 * 2.014 u)) * (0.027 u * c²) / E_megaton`.

The atomic-mass-unit conversion cancels between the event count and energy
per event.  With the recorded working constants, the result agrees to two
decimal places with `8.65 megatons of TNT`, answer C.

Blueprint label: `thm:physics:phyx_mini_0573:target`.
-/
theorem problem_phyx_mini_0573
    (setup : DeuteriumFusionBombSetup)
    (_problem : MatchesFusionBombProblemData setup)
    (_figure : MatchesPrimaryBombFigure setup)
    (_reference : MatchesReferenceFusionData setup)
    (_physical : HasPhysicalFusionParameters setup)
    (_laws : SatisfiesFusionYieldLaws setup) :
    setup.fusionRatingMegatonsTNT =
        (((3 / 10 : ℝ) * 500) /
            (5 * ((2014 / 1000 : ℝ) * atomicMassUnitInKilograms))) *
          (((27 / 1000 : ℝ) * atomicMassUnitInKilograms) *
            (300_000_000 : ℝ) ^ 2) /
          (4_184_000_000_000_000 : ℝ) ∧
      MatchesDisplayedRating
        setup.fusionRatingMegatonsTNT recordedAnswerChoice ∧
      recordedAnswerChoice = .C := by
  have h_amu : atomicMassUnitInKilograms ≠ 0 := by
    norm_num [atomicMassUnitInKilograms]
  have h_deuterium_mass :
      massInKilograms (setup.speciesRestMass .deuterium) =
        (2014 / 1000 : ℝ) * atomicMassUnitInKilograms := by
    exact
      (div_eq_iff h_amu).mp
        _reference.deuteriumNucleusMassAtomicUnits
  have h_mass_defect :
      massInKilograms setup.reactionMassDefect =
        (27 / 1000 : ℝ) * atomicMassUnitInKilograms := by
    exact
      (div_eq_iff h_amu).mp
        _reference.reactionMassDefectAtomicUnits
  have h_reactant_mass :
      reactantRestMassInKilograms setup setup.reaction =
        5 * ((2014 / 1000 : ℝ) * atomicMassUnitInKilograms) := by
    rw [_problem.statedFusionChannel]
    classical
    simp only [reactantRestMassInKilograms, fiveDeuteriumFusionReaction]
    rw [Finset.sum_eq_single .deuterium]
    · rw [h_deuterium_mass]
      norm_num
    · intro species _ hne
      fin_cases species <;> simp_all
    · simp
  have h_reacted_mass :
      massInKilograms setup.reactedDeuteriumMass =
        (3 / 10 : ℝ) * 500 := by
    rw [_laws.reactedMassFromFraction,
      _problem.thirtyPercentUndergoesFusion,
      _problem.totalDeuteriumMassKilograms]
  have h_event_count :
      setup.reactionEventCount =
        ((3 / 10 : ℝ) * 500) /
          (5 * ((2014 / 1000 : ℝ) * atomicMassUnitInKilograms)) := by
    rw [_laws.eventCountFromReactedFuel, h_reacted_mass, h_reactant_mass]
  have h_energy_per_event :
      energyInJoules setup.energyReleasedPerEvent =
        ((27 / 1000 : ℝ) * atomicMassUnitInKilograms) *
          (300_000_000 : ℝ) ^ 2 := by
    rw [_laws.massEnergyEquivalencePerEvent, h_mass_defect,
      _reference.workingSpeedOfLightMetersPerSecond]
  have h_total_energy :
      energyInJoules setup.totalFusionEnergy =
        (((3 / 10 : ℝ) * 500) /
            (5 * ((2014 / 1000 : ℝ) * atomicMassUnitInKilograms))) *
          (((27 / 1000 : ℝ) * atomicMassUnitInKilograms) *
            (300_000_000 : ℝ) ^ 2) := by
    rw [_laws.totalEnergyFromAllEvents, h_event_count, h_energy_per_event]
  have h_rating :
      setup.fusionRatingMegatonsTNT =
        (((3 / 10 : ℝ) * 500) /
            (5 * ((2014 / 1000 : ℝ) * atomicMassUnitInKilograms))) *
          (((27 / 1000 : ℝ) * atomicMassUnitInKilograms) *
            (300_000_000 : ℝ) ^ 2) /
          (4_184_000_000_000_000 : ℝ) := by
    rw [_laws.megatonRatingFromEnergy, h_total_energy,
      _reference.oneMegatonTNTInJoules]
  refine ⟨h_rating, ?_, rfl⟩
  rw [h_rating]
  norm_num [MatchesDisplayedRating, recordedAnswerChoice,
    AnswerChoice.ratingMegatonsTNT, atomicMassUnitInKilograms, abs_of_nonneg,
    abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0573
