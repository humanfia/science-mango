import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0930

open Dimension

/-!
# Induced current around a solenoid with a piecewise-linear drive current

The primary raster `930.png` shows a `4.0 cm`-diameter resistive circular loop
surrounding a `2.0 cm`-diameter solenoid.  The solenoid is `10 cm` long, has
`100` turns, and its signed current is graphed from `0 s` to `3 s`.  Positive
solenoid current is clockwise as seen from the left.  The current is constant
at `-20 A` throughout the final graph segment, which contains the requested
observation time `2.5 s`.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only at coherent-SI readout boundaries, as graph coordinates
whose units are named in their fields, and in displayed answer choices.

Assumption/target split:

* governing laws: the solenoid-current rate is the derivative of the graphed
  current, the ideal-solenoid field and field-rate laws, uniform flux linkage
  over the solenoid cross-section, Faraday's law, and signed Ohm's law;
* previous-part results: none;
* figure/data readouts: the two diameters, solenoid length, turn count, loop
  resistance, current convention, graph axes and all three graph segments, and
  the observation time;
* current target conclusion: the loop current at `2.5 s` is `0 μA`, uniquely
  selecting displayed answer B.

Neither the zero loop current nor answer B occurs in a setup, figure, scenario,
positivity, geometry, derivative, or governing-law premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The time derivative of current has dimension charge per time squared. -/
def electricCurrentRateDimension : Dimension :=
  electricCurrentDimension * T𝓭⁻¹

/-- Magnetic permeability has dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A magnetic-flux-density change rate has one additional inverse time. -/
def magneticFluxDensityRateDimension : Dimension :=
  magneticFluxDensityDimension * T𝓭⁻¹

/-- Area has dimension length squared. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Magnetic flux is magnetic flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Electromotive force has the same dimension as magnetic-flux change rate. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electrical resistance has the dimension emf divided by current. -/
def electricalResistanceDimension : Dimension :=
  electromotiveForceDimension * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A signed electric current relative to a stated circuit orientation. -/
abbrev SignedElectricCurrent : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed time derivative of electric current. -/
abbrev SignedElectricCurrentRate : Type :=
  Dimensionful (WithDim electricCurrentRateDimension ℝ)

/-- A nonnegative magnetic permeability. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A signed axial component of magnetic flux density. -/
abbrev SignedMagneticFluxDensity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension ℝ)

/-- A signed time derivative of an axial magnetic-flux-density component. -/
abbrev SignedMagneticFluxDensityRate : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension ℝ)

/-- Signed magnetic flux relative to the selected surface normal. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Signed magnetic-flux change rate. -/
abbrev SignedMagneticFluxRate : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed electromotive force relative to the positive loop orientation. -/
abbrev SignedElectromotiveForce : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- A nonnegative electrical resistance. -/
abbrev ElectricalResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read a length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical time in seconds. -/
def timeInSeconds (time : TimeMagnitude) : ℝ :=
  nonnegativeSIReadout time

/-- Read an area in square metres. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  nonnegativeSIReadout area

/-- Read a signed electric current in amperes. -/
def signedCurrentInAmperes (current : SignedElectricCurrent) : ℝ :=
  signedSIReadout current

/-- Read a signed electric current in microamperes. -/
def signedCurrentInMicroamperes (current : SignedElectricCurrent) : ℝ :=
  1000000 * signedCurrentInAmperes current

/-- Read a signed current-change rate in amperes per second. -/
def signedCurrentRateInAmperesPerSecond
    (rate : SignedElectricCurrentRate) : ℝ :=
  signedSIReadout rate

/-- Read magnetic permeability in newtons per ampere squared. -/
def magneticPermeabilityInNewtonsPerAmpereSquared
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout permeability

/-- Read a signed axial magnetic-flux-density component in teslas. -/
def signedMagneticFluxDensityInTeslas
    (density : SignedMagneticFluxDensity) : ℝ :=
  signedSIReadout density

/-- Read a signed flux-density change rate in teslas per second. -/
def signedMagneticFluxDensityRateInTeslasPerSecond
    (rate : SignedMagneticFluxDensityRate) : ℝ :=
  signedSIReadout rate

/-- Read signed magnetic flux in webers. -/
def signedMagneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  signedSIReadout flux

/-- Read signed magnetic-flux change rate in webers per second. -/
def signedMagneticFluxRateInWebersPerSecond
    (rate : SignedMagneticFluxRate) : ℝ :=
  signedSIReadout rate

/-- Read signed electromotive force in volts. -/
def signedEmfInVolts (emf : SignedElectromotiveForce) : ℝ :=
  signedSIReadout emf

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-! ## Apparatus, orientations, and primary-raster vocabulary -/

/-- Sense of circulation as viewed along the line of sight. -/
inductive CircuitSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The side from which the circular windings are viewed in the problem. -/
inductive ViewingSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Axial directions distinguished relative to the observer at the left. -/
inductive SolenoidAxialDirection where
  | towardLeftViewer
  | awayFromLeftViewer
  deriving DecidableEq, Repr

/-- Idealization of the wound conductor. -/
inductive SolenoidModel where
  | idealUniformLongSolenoid
  | other
  deriving DecidableEq, Repr

/-- Idealization of the surrounding orange conducting loop. -/
inductive SurroundingLoopModel where
  | closedSingleTurnResistiveLoop
  | other
  deriving DecidableEq, Repr

/-- Physical and graphical objects visible in `930.png`. -/
inductive FigureObject where
  | surroundingLoop
  | solenoid
  | solenoidWindings
  | solenoidCurrentArrow
  | currentTimeGraph
  | timeAxis
  | currentAxis
  deriving DecidableEq, Fintype, Repr

/-- Symbolic or dimensional labels printed in `930.png`. -/
inductive FigureLabel where
  | loopDiameterFourCentimeters
  | solenoidDiameterTwoCentimeters
  | solenoidCurrent
  | timeInSeconds
  | currentInAmperes
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data from the primary raster.  Axis coordinates and
printed diameter values are scalar readouts in the units named by their fields.
-/
structure SolenoidLoopFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  loopSurroundsSolenoid : Bool
  displayedLoopDiameterCentimeters : ℝ
  displayedSolenoidDiameterCentimeters : ℝ
  displayedCurrentArrowSense : CircuitSense
  displayedCurrentArrowViewingSide : ViewingSide
  timeAxisMinimumSeconds : ℝ
  timeAxisMaximumSeconds : ℝ
  currentAxisMinimumAmperes : ℝ
  currentAxisMaximumAmperes : ℝ

/-!
Independent physical observables of the coupled solenoid-loop system.

Functions ending in `AtSecond` take a real coordinate explicitly measured in
seconds.  Their values remain unit-independent physical quantities.  The
field component and linked flux are positive along `positiveAxialDirection`;
emf and loop current are positive in `loopPositiveCurrentSense`.
-/
structure SolenoidLoopSetup where
  solenoidModel : SolenoidModel
  loopModel : SurroundingLoopModel
  loopDiameter : LengthMagnitude
  solenoidDiameter : LengthMagnitude
  solenoidLength : LengthMagnitude
  solenoidCrossSectionalArea : AreaMagnitude
  turnCount : ℕ
  loopResistance : ElectricalResistanceMagnitude
  vacuumPermeability : MagneticPermeabilityMagnitude
  observationTime : TimeMagnitude
  solenoidPositiveCurrentSense : CircuitSense
  positiveCurrentViewingSide : ViewingSide
  positiveAxialDirection : SolenoidAxialDirection
  loopPositiveCurrentSense : CircuitSense
  solenoidCurrentAtSecond : ℝ → SignedElectricCurrent
  solenoidCurrentChangeRateAtSecond : ℝ → SignedElectricCurrentRate
  solenoidAxialFluxDensityAtSecond : ℝ → SignedMagneticFluxDensity
  solenoidAxialFluxDensityChangeRateAtSecond :
    ℝ → SignedMagneticFluxDensityRate
  linkedMagneticFluxAtSecond : ℝ → SignedMagneticFlux
  linkedMagneticFluxChangeRateAtSecond : ℝ → SignedMagneticFluxRate
  inducedEmfAtSecond : ℝ → SignedElectromotiveForce
  loopCurrentAtSecond : ℝ → SignedElectricCurrent
  figure : SolenoidLoopFigure

/-! ## Scenario, figure evidence, and governing laws -/

/-- Prose-supplied apparatus data and the requested observation time. -/
structure MatchesStatedSolenoidLoopScenario
    (setup : SolenoidLoopSetup) : Prop where
  idealSolenoidModel :
    setup.solenoidModel = .idealUniformLongSolenoid
  surroundingLoopIsClosedAndResistive :
    setup.loopModel = .closedSingleTurnResistiveLoop
  solenoidLengthIsTenCentimeters :
    lengthInCentimeters setup.solenoidLength = 10
  solenoidHasOneHundredTurns : setup.turnCount = 100
  loopResistanceIsOneTenthOhm :
    resistanceInOhms setup.loopResistance = 1 / 10
  observationTimeIsTwoPointFiveSeconds :
    timeInSeconds setup.observationTime = 5 / 2
  positiveSolenoidCurrentIsClockwise :
    setup.solenoidPositiveCurrentSense = .clockwise
  currentConventionIsViewedFromLeft :
    setup.positiveCurrentViewingSide = .left
  positiveCurrentProducesFieldAwayFromLeftViewer :
    setup.positiveAxialDirection = .awayFromLeftViewer
  positiveLoopBoundaryIsClockwiseFromLeft :
    setup.loopPositiveCurrentSense = .clockwise

/-!
Primary-raster geometry, labels, axes, and the complete three-piece current
trace.  The graph calibrates only the solenoid current; it contains no loop
current or induced-emf answer.
-/
structure MatchesSuppliedSolenoidLoopFigure
    (setup : SolenoidLoopSetup) : Prop where
  everyObjectIsShown : ∀ object, setup.figure.objectShown object = true
  everyLabelIsShown : ∀ label, setup.figure.labelShown label = true
  loopIsDrawnAroundSolenoid : setup.figure.loopSurroundsSolenoid = true
  printedLoopDiameter :
    setup.figure.displayedLoopDiameterCentimeters = 4
  printedSolenoidDiameter :
    setup.figure.displayedSolenoidDiameterCentimeters = 2
  loopDiameterMatchesPrintedLabel :
    lengthInCentimeters setup.loopDiameter =
      setup.figure.displayedLoopDiameterCentimeters
  solenoidDiameterMatchesPrintedLabel :
    lengthInCentimeters setup.solenoidDiameter =
      setup.figure.displayedSolenoidDiameterCentimeters
  displayedArrowIsClockwise :
    setup.figure.displayedCurrentArrowSense = .clockwise
  displayedArrowIsViewedFromLeft :
    setup.figure.displayedCurrentArrowViewingSide = .left
  graphTimeAxisStartsAtZero : setup.figure.timeAxisMinimumSeconds = 0
  graphTimeAxisEndsAtThree : setup.figure.timeAxisMaximumSeconds = 3
  graphCurrentAxisMinimum : setup.figure.currentAxisMinimumAmperes = -20
  graphCurrentAxisMaximum : setup.figure.currentAxisMaximumAmperes = 20
  initialTwentyAmperePlateau : ∀ timeInSeconds,
    timeInSeconds ∈ Set.Icc (0 : ℝ) 1 →
      signedCurrentInAmperes
          (setup.solenoidCurrentAtSecond timeInSeconds) = 20
  linearFortyAmperePerSecondTransition : ∀ timeInSeconds,
    timeInSeconds ∈ Set.Icc (1 : ℝ) 2 →
      signedCurrentInAmperes
          (setup.solenoidCurrentAtSecond timeInSeconds) =
        60 - 40 * timeInSeconds
  finalNegativeTwentyAmperePlateau : ∀ timeInSeconds,
    timeInSeconds ∈ Set.Icc (2 : ℝ) 3 →
      signedCurrentInAmperes
          (setup.solenoidCurrentAtSecond timeInSeconds) = -20

/-- Positivity and geometric containment conditions for the physical setup. -/
structure HasPhysicalSolenoidLoopParameters
    (setup : SolenoidLoopSetup) : Prop where
  loopDiameterPositive : 0 < lengthInMeters setup.loopDiameter
  solenoidDiameterPositive : 0 < lengthInMeters setup.solenoidDiameter
  solenoidLengthPositive : 0 < lengthInMeters setup.solenoidLength
  solenoidAreaPositive :
    0 < areaInSquareMeters setup.solenoidCrossSectionalArea
  loopResistancePositive : 0 < resistanceInOhms setup.loopResistance
  vacuumPermeabilityPositive :
    0 < magneticPermeabilityInNewtonsPerAmpereSquared
      setup.vacuumPermeability
  solenoidFitsStrictlyInsideLoop :
    lengthInMeters setup.solenoidDiameter < lengthInMeters setup.loopDiameter

/-! Circular geometry fixes the area through which ideal-solenoid flux links. -/
structure SatisfiesCircularSolenoidGeometry
    (setup : SolenoidLoopSetup) : Prop where
  crossSectionalAreaLaw :
    areaInSquareMeters setup.solenoidCrossSectionalArea =
      Real.pi * (lengthInMeters setup.solenoidDiameter / 2) ^ 2

/-!
The rate observable is the derivative of the graphed signed current away from
the two corners of the piecewise-linear trace.
-/
structure SatisfiesSolenoidCurrentRateDefinition
    (setup : SolenoidLoopSetup) : Prop where
  rateIsDerivativeAwayFromGraphCorners : ∀ timeInSeconds : ℝ,
    0 < timeInSeconds →
    timeInSeconds < 3 →
    timeInSeconds ≠ 1 →
    timeInSeconds ≠ 2 →
      HasDerivAt
        (fun time =>
          signedCurrentInAmperes (setup.solenoidCurrentAtSecond time))
        (signedCurrentRateInAmperesPerSecond
          (setup.solenoidCurrentChangeRateAtSecond timeInSeconds))
        timeInSeconds

/-!
The ideal long-solenoid law `B = μ₀ (N / ℓ) I` and its rate form.  These laws
mention neither the surrounding-loop current nor any displayed answer value.
-/
structure SatisfiesIdealSolenoidFieldLaw
    (setup : SolenoidLoopSetup) : Prop where
  axialFieldLaw : ∀ timeInSeconds,
    signedMagneticFluxDensityInTeslas
        (setup.solenoidAxialFluxDensityAtSecond timeInSeconds) =
      magneticPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        (setup.turnCount : ℝ) /
          lengthInMeters setup.solenoidLength *
            signedCurrentInAmperes
              (setup.solenoidCurrentAtSecond timeInSeconds)
  axialFieldRateLaw : ∀ timeInSeconds,
    signedMagneticFluxDensityRateInTeslasPerSecond
        (setup.solenoidAxialFluxDensityChangeRateAtSecond timeInSeconds) =
      magneticPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        (setup.turnCount : ℝ) /
          lengthInMeters setup.solenoidLength *
            signedCurrentRateInAmperesPerSecond
              (setup.solenoidCurrentChangeRateAtSecond timeInSeconds)

/-!
The larger loop links the field only over the solenoid cross-section.  Thus
flux and flux rate are the signed axial field component and its rate times the
same physical cross-sectional area.
-/
structure SatisfiesUniformSolenoidFluxLinkageLaw
    (setup : SolenoidLoopSetup) : Prop where
  linkedFluxLaw : ∀ timeInSeconds,
    signedMagneticFluxInWebers
        (setup.linkedMagneticFluxAtSecond timeInSeconds) =
      signedMagneticFluxDensityInTeslas
          (setup.solenoidAxialFluxDensityAtSecond timeInSeconds) *
        areaInSquareMeters setup.solenoidCrossSectionalArea
  linkedFluxRateLaw : ∀ timeInSeconds,
    signedMagneticFluxRateInWebersPerSecond
        (setup.linkedMagneticFluxChangeRateAtSecond timeInSeconds) =
      signedMagneticFluxDensityRateInTeslasPerSecond
          (setup.solenoidAxialFluxDensityChangeRateAtSecond timeInSeconds) *
        areaInSquareMeters setup.solenoidCrossSectionalArea

/-- Faraday's induction law in the selected positive boundary orientation. -/
structure SatisfiesFaradayInductionLaw
    (setup : SolenoidLoopSetup) : Prop where
  faradayLaw : ∀ timeInSeconds,
    signedEmfInVolts (setup.inducedEmfAtSecond timeInSeconds) =
      -signedMagneticFluxRateInWebersPerSecond
        (setup.linkedMagneticFluxChangeRateAtSecond timeInSeconds)

/-! Signed Ohm's law for the passive surrounding loop. -/
structure SatisfiesResistiveLoopOhmsLaw
    (setup : SolenoidLoopSetup) : Prop where
  ohmsLaw : ∀ timeInSeconds,
    signedEmfInVolts (setup.inducedEmfAtSecond timeInSeconds) =
      signedCurrentInAmperes (setup.loopCurrentAtSecond timeInSeconds) *
        resistanceInOhms setup.loopResistance

/-! ## Displayed answers and requested conclusion -/

/-- Labels of the four current-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current in microamperes printed beside each answer choice. -/
def AnswerChoice.displayedCurrentInMicroamperes : AnswerChoice → ℝ
  | .A => 8 / 5
  | .B => 0
  | .C => 16 / 5
  | .D => 4 / 5

/-- Dataset-recorded answer label. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Signed loop-current readout at the independently modeled observation time. -/
def observedLoopCurrentInMicroamperes (setup : SolenoidLoopSetup) : ℝ :=
  signedCurrentInMicroamperes
    (setup.loopCurrentAtSecond (timeInSeconds setup.observationTime))

/-- A displayed choice agrees exactly with the requested current readout. -/
def AnswerMatchesObservedLoopCurrent
    (setup : SolenoidLoopSetup) (choice : AnswerChoice) : Prop :=
  observedLoopCurrentInMicroamperes setup =
    choice.displayedCurrentInMicroamperes

/-- A choice is the unique displayed answer matching the requested current. -/
def IsUniqueMatchingAnswer
    (setup : SolenoidLoopSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesObservedLoopCurrent setup choice ∧
    ∀ otherChoice,
      AnswerMatchesObservedLoopCurrent setup otherChoice →
        otherChoice = choice

/-!
At `2.5 s`, the solenoid-current graph is flat, so its time derivative and the
magnetic-flux change rate vanish.  Faraday's law then gives zero emf; since the
surrounding loop has positive resistance, signed Ohm's law gives zero loop
current.  This formalizes `thm:physics:phyx_mini_0930:target`.
-/
theorem problem_phyx_mini_0930
    (setup : SolenoidLoopSetup)
    (_scenario : MatchesStatedSolenoidLoopScenario setup)
    (_figure : MatchesSuppliedSolenoidLoopFigure setup)
    (_physical : HasPhysicalSolenoidLoopParameters setup)
    (_geometry : SatisfiesCircularSolenoidGeometry setup)
    (_currentRate : SatisfiesSolenoidCurrentRateDefinition setup)
    (_solenoidField : SatisfiesIdealSolenoidFieldLaw setup)
    (_fluxLinkage : SatisfiesUniformSolenoidFluxLinkageLaw setup)
    (_faraday : SatisfiesFaradayInductionLaw setup)
    (_ohm : SatisfiesResistiveLoopOhmsLaw setup) :
    observedLoopCurrentInMicroamperes setup = 0 ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  have hCurrentEventuallyConstant :
      (fun timeInSeconds : ℝ =>
        signedCurrentInAmperes (setup.solenoidCurrentAtSecond timeInSeconds)) =ᶠ[
          nhds (5 / 2 : ℝ)] (fun _ => -20) := by
    filter_upwards [
      Ioo_mem_nhds (show (2 : ℝ) < 5 / 2 by norm_num)
        (show (5 / 2 : ℝ) < 3 by norm_num)] with timeInSeconds hTime
    exact _figure.finalNegativeTwentyAmperePlateau timeInSeconds
      ⟨hTime.1.le, hTime.2.le⟩
  have hCurrentDerivativeZero :
      HasDerivAt
        (fun timeInSeconds : ℝ =>
          signedCurrentInAmperes (setup.solenoidCurrentAtSecond timeInSeconds))
        0 (5 / 2 : ℝ) :=
    (hasDerivAt_const (5 / 2 : ℝ) (-20 : ℝ)).congr_of_eventuallyEq
      hCurrentEventuallyConstant
  have hCurrentRate :
      signedCurrentRateInAmperesPerSecond
          (setup.solenoidCurrentChangeRateAtSecond (5 / 2 : ℝ)) = 0 := by
    exact
      (_currentRate.rateIsDerivativeAwayFromGraphCorners (5 / 2 : ℝ)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)).unique
        hCurrentDerivativeZero
  have hFieldRate :
      signedMagneticFluxDensityRateInTeslasPerSecond
          (setup.solenoidAxialFluxDensityChangeRateAtSecond (5 / 2 : ℝ)) = 0 := by
    simpa [hCurrentRate] using
      _solenoidField.axialFieldRateLaw (5 / 2 : ℝ)
  have hFluxRate :
      signedMagneticFluxRateInWebersPerSecond
          (setup.linkedMagneticFluxChangeRateAtSecond (5 / 2 : ℝ)) = 0 := by
    simpa [hFieldRate] using
      _fluxLinkage.linkedFluxRateLaw (5 / 2 : ℝ)
  have hEmf :
      signedEmfInVolts (setup.inducedEmfAtSecond (5 / 2 : ℝ)) = 0 := by
    simpa [hFluxRate] using _faraday.faradayLaw (5 / 2 : ℝ)
  have hLoopCurrentAmperes :
      signedCurrentInAmperes (setup.loopCurrentAtSecond (5 / 2 : ℝ)) = 0 := by
    have hOhm := _ohm.ohmsLaw (5 / 2 : ℝ)
    rw [hEmf] at hOhm
    exact (mul_eq_zero.mp hOhm.symm).resolve_right
      (ne_of_gt _physical.loopResistancePositive)
  have hObserved : observedLoopCurrentInMicroamperes setup = 0 := by
    simp [observedLoopCurrentInMicroamperes, signedCurrentInMicroamperes,
      _scenario.observationTimeIsTwoPointFiveSeconds, hLoopCurrentAmperes]
  refine ⟨hObserved, ?_⟩
  constructor
  · simp [AnswerMatchesObservedLoopCurrent, recordedDatasetAnswer,
      AnswerChoice.displayedCurrentInMicroamperes, hObserved]
  · intro otherChoice hOtherChoice
    cases otherChoice with
    | A =>
        norm_num [AnswerMatchesObservedLoopCurrent,
          AnswerChoice.displayedCurrentInMicroamperes, hObserved] at hOtherChoice
    | B => rfl
    | C =>
        norm_num [AnswerMatchesObservedLoopCurrent,
          AnswerChoice.displayedCurrentInMicroamperes, hObserved] at hOtherChoice
    | D =>
        norm_num [AnswerMatchesObservedLoopCurrent,
          AnswerChoice.displayedCurrentInMicroamperes, hObserved] at hOtherChoice

end PhyXMiniProblems.ProblemPhyXMini0930
