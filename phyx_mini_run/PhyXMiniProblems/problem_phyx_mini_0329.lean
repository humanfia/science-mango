import Mathlib.Analysis.Real.Sqrt
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Radio-wave interference from a rising atmospheric reflecting layer

A source `S` and detector `D` lie on level ground, separated by the physical
distance `d`.  One radio wave travels directly from `S` to `D`; a coherent
second wave follows a symmetric two-leg path through a reflecting atmospheric
layer above the midpoint.  The layer first has height `H` and then rises by
`h` to height `H + h`.

All distances and wavelengths are unit-independent Physlib quantities with
length dimension.  Real scalars occur only as coherent readouts in a selected
length unit, signed figure coordinates, and dimensionless phase differences
measured in wavelength cycles.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0329

open Dimension

/-! ## Dimensionful lengths and figure vocabulary -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length used for Cartesian coordinates in the figure. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed figure coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- A physical point in the vertical plane of the supplied diagram. -/
structure PlanePoint where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- Coordinate readout of a physical point in a selected length unit. -/
def horizontalReadout (unit : LengthUnit) (point : PlanePoint) : ℝ :=
  signedLengthReadout unit point.horizontal

/-- Vertical-coordinate readout of a physical point in a selected unit. -/
def verticalReadout (unit : LengthUnit) (point : PlanePoint) : ℝ :=
  signedLengthReadout unit point.vertical

/-- Point labels visible or geometrically distinguished in the primary image. -/
inductive FigurePointLabel where
  | sourceS
  | midpoint
  | detectorD
  | reflectionAtH
  | reflectionAtHPlusH
  deriving DecidableEq, Repr

/-- The direct and atmospheric-reflection propagation routes. -/
inductive PropagationRoute where
  | direct
  | atmosphericReflection
  deriving DecidableEq, Repr

/-- Qualitative electromagnetic-wave kind used in the problem statement. -/
inductive ElectromagneticWaveKind where
  | radio
  | other
  deriving DecidableEq, Repr

/-- The propagation medium between the ground apparatus and reflecting layer. -/
inductive PropagationMedium where
  | atmosphere
  | other
  deriving DecidableEq, Repr

/-!
Primary-image objects and marks.  Coordinates are physical lengths; the
Boolean fields record only what the bitmap depicts and do not impose an
interference result.
-/
structure RisingLayerFigure where
  point : FigurePointLabel → PlanePoint
  showsDirectHorizontalArrow : Bool
  showsInitialSolidReflectedPath : Bool
  showsRaisedDashedReflectedPath : Bool
  showsVerticalDashedMidline : Bool
  showsTwoHalfDistanceLabels : Bool
  showsInitialHeightHLabel : Bool
  showsAdditionalRisehLabel : Bool

/-! ## Independent physical setup and observables -/

/-!
The path lengths, wavelength, and phase observables are independent physical
quantities.  In particular, `wavelengthLambda` is not defined from the
multiple-choice answer.  The predicates below supply the geometric and wave
laws relating these quantities.
-/
structure AtmosphericLayerInterferenceSetup where
  waveKind : ElectromagneticWaveKind
  medium : PropagationMedium
  figure : RisingLayerFigure
  sourceDetectorSeparationD : LengthQuantity
  initialLayerHeightH : LengthQuantity
  layerRiseh : LengthQuantity
  raisedLayerHeightHPlusH : LengthQuantity
  wavelengthLambda : LengthQuantity
  directPathLength : LengthQuantity
  reflectedPathLengthAtHeight : LengthQuantity → LengthQuantity
  excessPathLengthAtHeight : LengthQuantity → LengthQuantity
  phaseDifferenceCyclesAtHeight : LengthQuantity → ℝ
  waveReachesDetectorVia : PropagationRoute → Prop
  directAndReflectedWavesAreCoherent : Prop
  atmosphericLayerReflectsRadioWave : Prop
  reflectionPhaseContributionIsConstantDuringRise : Prop
  layerRisesGradually : Prop

/-! ## Problem statement and primary-figure readouts -/

/-- Qualitative information stated in the physical scenario. -/
structure MatchesRadioReflectionScenario
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  waveIsRadio : setup.waveKind = .radio
  mediumIsAtmosphere : setup.medium = .atmosphere
  directWaveReachesDetector : setup.waveReachesDetectorVia .direct
  reflectedWaveReachesDetector :
    setup.waveReachesDetectorVia .atmosphericReflection
  wavesAreCoherent : setup.directAndReflectedWavesAreCoherent
  layerReflectsWave : setup.atmosphericLayerReflectsRadioWave
  constantReflectionContribution :
    setup.reflectionPhaseContributionIsConstantDuringRise
  gradualRise : setup.layerRisesGradually

/-!
Geometry read directly from the supplied bitmap: `S`, the midpoint, and `D`
are on one horizontal ground line; both reflection points lie vertically above
the midpoint; the two ground halves are each `d/2`; the lower apex is at `H`
and the upper apex is an additional `h` higher.
-/
structure MatchesSuppliedFigure
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  sourceOnGround : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .sourceS) = 0
  midpointOnGround : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .midpoint) = 0
  detectorOnGround : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .detectorD) = 0
  sourceToMidpointIsHalfD : ∀ unit : LengthUnit,
    horizontalReadout unit (setup.figure.point .midpoint) -
        horizontalReadout unit (setup.figure.point .sourceS) =
      lengthReadout unit setup.sourceDetectorSeparationD / 2
  midpointToDetectorIsHalfD : ∀ unit : LengthUnit,
    horizontalReadout unit (setup.figure.point .detectorD) -
        horizontalReadout unit (setup.figure.point .midpoint) =
      lengthReadout unit setup.sourceDetectorSeparationD / 2
  initialReflectionAboveMidpoint : ∀ unit : LengthUnit,
    horizontalReadout unit (setup.figure.point .reflectionAtH) =
      horizontalReadout unit (setup.figure.point .midpoint)
  raisedReflectionAboveMidpoint : ∀ unit : LengthUnit,
    horizontalReadout unit (setup.figure.point .reflectionAtHPlusH) =
      horizontalReadout unit (setup.figure.point .midpoint)
  initialApexHeight : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .reflectionAtH) -
        verticalReadout unit (setup.figure.point .midpoint) =
      lengthReadout unit setup.initialLayerHeightH
  riseBetweenApices : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .reflectionAtHPlusH) -
        verticalReadout unit (setup.figure.point .reflectionAtH) =
      lengthReadout unit setup.layerRiseh
  raisedHeightIsHPlush : ∀ unit : LengthUnit,
    lengthReadout unit setup.raisedLayerHeightHPlusH =
      lengthReadout unit setup.initialLayerHeightH +
        lengthReadout unit setup.layerRiseh
  raisedApexHeight : ∀ unit : LengthUnit,
    verticalReadout unit (setup.figure.point .reflectionAtHPlusH) -
        verticalReadout unit (setup.figure.point .midpoint) =
      lengthReadout unit setup.raisedLayerHeightHPlusH
  directArrowShown : setup.figure.showsDirectHorizontalArrow = true
  initialReflectedPathShown :
    setup.figure.showsInitialSolidReflectedPath = true
  raisedReflectedPathShown :
    setup.figure.showsRaisedDashedReflectedPath = true
  verticalMidlineShown : setup.figure.showsVerticalDashedMidline = true
  halfDistanceLabelsShown : setup.figure.showsTwoHalfDistanceLabels = true
  initialHeightLabelShown : setup.figure.showsInitialHeightHLabel = true
  riseLabelShown : setup.figure.showsAdditionalRisehLabel = true

/-- Positivity and nondegeneracy of all physical lengths in the scenario. -/
structure HasPhysicalParameters
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  separationPositive :
    0 < lengthReadout LengthUnit.meters setup.sourceDetectorSeparationD
  initialHeightPositive :
    0 < lengthReadout LengthUnit.meters setup.initialLayerHeightH
  risePositive : 0 < lengthReadout LengthUnit.meters setup.layerRiseh
  wavelengthPositive :
    0 < lengthReadout LengthUnit.meters setup.wavelengthLambda
  directPathPositive :
    0 < lengthReadout LengthUnit.meters setup.directPathLength
  reflectedPathsNonnegative : ∀ height : LengthQuantity,
    0 ≤ lengthReadout LengthUnit.meters height →
      0 ≤ lengthReadout LengthUnit.meters
        (setup.reflectedPathLengthAtHeight height)
  excessPathsNonnegative : ∀ height : LengthQuantity,
    0 ≤ lengthReadout LengthUnit.meters height →
      0 ≤ lengthReadout LengthUnit.meters
        (setup.excessPathLengthAtHeight height)

/-! ## Governing geometry and phase laws -/

/-!
Symmetric specular-reflection geometry.  At a layer height `y`, each leg has
horizontal projection `d/2` and vertical projection `y`, so the total
reflected length is `2 * sqrt (y^2 + (d/2)^2)`.  This general law is stated for
every height and unit; it does not contain the requested wavelength formula.
-/
structure SatisfiesSymmetricReflectionGeometry
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  directPath : ∀ unit : LengthUnit,
    lengthReadout unit setup.directPathLength =
      lengthReadout unit setup.sourceDetectorSeparationD
  reflectedPath : ∀ (unit : LengthUnit) (height : LengthQuantity),
    lengthReadout unit (setup.reflectedPathLengthAtHeight height) =
      2 * Real.sqrt
        (lengthReadout unit height ^ 2 +
          (lengthReadout unit setup.sourceDetectorSeparationD / 2) ^ 2)
  excessPath : ∀ (unit : LengthUnit) (height : LengthQuantity),
    lengthReadout unit (setup.excessPathLengthAtHeight height) =
      lengthReadout unit (setup.reflectedPathLengthAtHeight height) -
        lengthReadout unit setup.directPathLength

/-!
Changing only the reflecting-layer height changes phase by the corresponding
change of path excess divided by the wavelength.  Any fixed phase contribution
from reflection cancels between the two heights.  Phase is measured in the
dimensionless unit of wavelength cycles.
-/
structure SatisfiesTwoPathPhaseLaw
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  phaseChangeFromPathChange :
    ∀ (unit : LengthUnit) (lowerHeight upperHeight : LengthQuantity),
      setup.phaseDifferenceCyclesAtHeight upperHeight -
          setup.phaseDifferenceCyclesAtHeight lowerHeight =
        (lengthReadout unit (setup.excessPathLengthAtHeight upperHeight) -
            lengthReadout unit (setup.excessPathLengthAtHeight lowerHeight)) /
          lengthReadout unit setup.wavelengthLambda

/-! ## Interference observations during the rise -/

/-- At an in-phase height, the phase difference is an integral cycle count. -/
def WavesAreInPhaseAt
    (setup : AtmosphericLayerInterferenceSetup)
    (height : LengthQuantity) : Prop :=
  ∃ cycle : ℤ,
    setup.phaseDifferenceCyclesAtHeight height = (cycle : ℝ)

/-- At an out-of-phase height, the phase differs by a half-integral cycle. -/
def WavesAreOutOfPhaseAt
    (setup : AtmosphericLayerInterferenceSetup)
    (height : LengthQuantity) : Prop :=
  ∃ cycle : ℤ,
    setup.phaseDifferenceCyclesAtHeight height = (cycle : ℝ) + 1 / 2

/-!
The stated observation is the first opposition reached as the layer rises:
the waves start in phase at `H` and, after the gradual rise by `h`, have
advanced by exactly one half-cycle and are out of phase.  This is experimental
phase information, not an assumption of the requested wavelength value.
-/
structure ReachesFirstOppositionAfterRise
    (setup : AtmosphericLayerInterferenceSetup) : Prop where
  initiallyInPhase : WavesAreInPhaseAt setup setup.initialLayerHeightH
  finallyOutOfPhase :
    WavesAreOutOfPhaseAt setup setup.raisedLayerHeightHPlusH
  firstHalfCycleAdvance :
    setup.phaseDifferenceCyclesAtHeight setup.raisedLayerHeightHPlusH -
        setup.phaseDifferenceCyclesAtHeight setup.initialLayerHeightH =
      1 / 2

/-! ## Displayed answer choices and target -/

/-- Labels of the four wavelength formulas displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Scalar readout of a displayed formula in an arbitrary common length unit.
The quantities `H`, `h`, and `d` remain dimensionful in the setup and are
converted coherently before the displayed arithmetic is evaluated.
-/
def displayedWavelengthReadout
    (setup : AtmosphericLayerInterferenceSetup)
    (unit : LengthUnit) : AnswerChoice → ℝ
  | .A =>
      2 *
        (Real.sqrt
            (2 *
                (lengthReadout unit setup.initialLayerHeightH +
                  lengthReadout unit setup.layerRiseh) ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
          Real.sqrt
            (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2))
  | .B =>
      2 *
        (Real.sqrt
            (4 *
                (lengthReadout unit setup.initialLayerHeightH +
                  lengthReadout unit setup.layerRiseh) ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
          Real.sqrt
            (2 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2))
  | .C =>
      Real.sqrt
          (4 *
              (lengthReadout unit setup.initialLayerHeightH +
                lengthReadout unit setup.layerRiseh) ^ 2 +
            lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
        Real.sqrt
          (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
            lengthReadout unit setup.sourceDetectorSeparationD ^ 2)
  | .D =>
      2 *
        (Real.sqrt
            (4 *
                (lengthReadout unit setup.initialLayerHeightH +
                  lengthReadout unit setup.layerRiseh) ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
          Real.sqrt
            (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2))

/-- A displayed choice agrees with the physical wavelength in every unit. -/
def MatchesDisplayedWavelengthChoice
    (setup : AtmosphericLayerInterferenceSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ unit : LengthUnit,
    lengthReadout unit setup.wavelengthLambda =
      displayedWavelengthReadout setup unit choice

/-- A displayed wavelength formula is the unique matching answer. -/
def IsUniqueMatchingDisplayedChoice
    (setup : AtmosphericLayerInterferenceSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedWavelengthChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedWavelengthChoice setup other → other = choice

/-!
The half-cycle change and symmetric two-leg geometry give

`lambda = 2 * (sqrt (4 * (H + h)^2 + d^2) - sqrt (4 * H^2 + d^2))`,

which is exactly and uniquely displayed as choice D.  The formula appears
only in this conclusion (and in the neutral table of displayed choices), not
in a setup field, scenario predicate, geometric law, or phase law.

This formalizes blueprint label `thm:physics:phyx_mini_0329:target`.
-/
theorem problem_phyx_mini_0329
    (setup : AtmosphericLayerInterferenceSetup)
    (_scenario : MatchesRadioReflectionScenario setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_geometry : SatisfiesSymmetricReflectionGeometry setup)
    (_phaseLaw : SatisfiesTwoPathPhaseLaw setup)
    (_observation : ReachesFirstOppositionAfterRise setup) :
    (∀ unit : LengthUnit,
      lengthReadout unit setup.wavelengthLambda =
        2 *
          (Real.sqrt
              (4 *
                  (lengthReadout unit setup.initialLayerHeightH +
                    lengthReadout unit setup.layerRiseh) ^ 2 +
                lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
            Real.sqrt
              (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
                lengthReadout unit setup.sourceDetectorSeparationD ^ 2))) ∧
      IsUniqueMatchingDisplayedChoice setup .D := by
  have wavelength_formula : ∀ unit : LengthUnit,
      lengthReadout unit setup.wavelengthLambda =
        2 *
          (Real.sqrt
              (4 *
                  (lengthReadout unit setup.initialLayerHeightH +
                    lengthReadout unit setup.layerRiseh) ^ 2 +
                lengthReadout unit setup.sourceDetectorSeparationD ^ 2) -
            Real.sqrt
              (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
                lengthReadout unit setup.sourceDetectorSeparationD ^ 2)) := by
    intro unit
    have half_cycle :
        (1 : ℝ) / 2 =
          (lengthReadout unit
                (setup.excessPathLengthAtHeight
                  setup.raisedLayerHeightHPlusH) -
              lengthReadout unit
                (setup.excessPathLengthAtHeight
                  setup.initialLayerHeightH)) /
            lengthReadout unit setup.wavelengthLambda := by
      calc
        (1 : ℝ) / 2 =
            setup.phaseDifferenceCyclesAtHeight
                setup.raisedLayerHeightHPlusH -
              setup.phaseDifferenceCyclesAtHeight
                setup.initialLayerHeightH :=
          _observation.firstHalfCycleAdvance.symm
        _ = _ :=
          _phaseLaw.phaseChangeFromPathChange unit
            setup.initialLayerHeightH setup.raisedLayerHeightHPlusH
    have wavelength_ne :
        lengthReadout unit setup.wavelengthLambda ≠ 0 := by
      intro wavelength_zero
      rw [wavelength_zero, div_zero] at half_cycle
      norm_num at half_cycle
    have path_change :
        lengthReadout unit
              (setup.excessPathLengthAtHeight
                setup.raisedLayerHeightHPlusH) -
            lengthReadout unit
              (setup.excessPathLengthAtHeight
                setup.initialLayerHeightH) =
          ((1 : ℝ) / 2) *
            lengthReadout unit setup.wavelengthLambda :=
      (div_eq_iff wavelength_ne).mp half_cycle.symm
    have wavelength_from_path_change :
        lengthReadout unit setup.wavelengthLambda =
          2 *
            (lengthReadout unit
                  (setup.excessPathLengthAtHeight
                    setup.raisedLayerHeightHPlusH) -
              lengthReadout unit
                (setup.excessPathLengthAtHeight
                  setup.initialLayerHeightH)) := by
      linarith
    rw [_geometry.excessPath unit setup.raisedLayerHeightHPlusH,
      _geometry.excessPath unit setup.initialLayerHeightH,
      _geometry.reflectedPath unit setup.raisedLayerHeightHPlusH,
      _geometry.reflectedPath unit setup.initialLayerHeightH,
      _figure.raisedHeightIsHPlush unit] at wavelength_from_path_change
    have raised_root :
        Real.sqrt
            (4 *
                (lengthReadout unit setup.initialLayerHeightH +
                  lengthReadout unit setup.layerRiseh) ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2) =
          2 *
            Real.sqrt
              ((lengthReadout unit setup.initialLayerHeightH +
                    lengthReadout unit setup.layerRiseh) ^ 2 +
                (lengthReadout unit setup.sourceDetectorSeparationD / 2) ^ 2) := by
      rw [show
        4 *
              (lengthReadout unit setup.initialLayerHeightH +
                lengthReadout unit setup.layerRiseh) ^ 2 +
            lengthReadout unit setup.sourceDetectorSeparationD ^ 2 =
          4 *
            ((lengthReadout unit setup.initialLayerHeightH +
                  lengthReadout unit setup.layerRiseh) ^ 2 +
              (lengthReadout unit setup.sourceDetectorSeparationD / 2) ^ 2) by
        ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
        apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
        norm_num
      rw [sqrt_four]
    have initial_root :
        Real.sqrt
            (4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
              lengthReadout unit setup.sourceDetectorSeparationD ^ 2) =
          2 *
            Real.sqrt
              (lengthReadout unit setup.initialLayerHeightH ^ 2 +
                (lengthReadout unit setup.sourceDetectorSeparationD / 2) ^ 2) := by
      rw [show
        4 * lengthReadout unit setup.initialLayerHeightH ^ 2 +
            lengthReadout unit setup.sourceDetectorSeparationD ^ 2 =
          4 *
            (lengthReadout unit setup.initialLayerHeightH ^ 2 +
              (lengthReadout unit setup.sourceDetectorSeparationD / 2) ^ 2) by
        ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
        apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
        norm_num
      rw [sqrt_four]
    linarith
  refine ⟨wavelength_formula, ?_⟩
  constructor
  · intro unit
    simpa [displayedWavelengthReadout] using wavelength_formula unit
  · intro other other_matches
    have initial_height_pos :=
      _physical.initialHeightPositive
    have rise_pos := _physical.risePositive
    have wavelength_at_meters := wavelength_formula LengthUnit.meters
    cases other with
    | A =>
        have other_at_meters := other_matches LengthUnit.meters
        simp only [displayedWavelengthReadout] at other_at_meters
        have raised_sqrt_lt :
            Real.sqrt
                (2 *
                    (lengthReadout LengthUnit.meters
                          setup.initialLayerHeightH +
                      lengthReadout LengthUnit.meters setup.layerRiseh) ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) <
              Real.sqrt
                (4 *
                    (lengthReadout LengthUnit.meters
                          setup.initialLayerHeightH +
                      lengthReadout LengthUnit.meters setup.layerRiseh) ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · positivity
          · nlinarith
        linarith
    | B =>
        have other_at_meters := other_matches LengthUnit.meters
        simp only [displayedWavelengthReadout] at other_at_meters
        have initial_sqrt_lt :
            Real.sqrt
                (2 *
                    lengthReadout LengthUnit.meters
                        setup.initialLayerHeightH ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) <
              Real.sqrt
                (4 *
                    lengthReadout LengthUnit.meters
                        setup.initialLayerHeightH ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · positivity
          · nlinarith
        linarith
    | C =>
        have other_at_meters := other_matches LengthUnit.meters
        simp only [displayedWavelengthReadout] at other_at_meters
        have initial_sqrt_lt_raised :
            Real.sqrt
                (4 *
                    lengthReadout LengthUnit.meters
                        setup.initialLayerHeightH ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) <
              Real.sqrt
                (4 *
                    (lengthReadout LengthUnit.meters
                          setup.initialLayerHeightH +
                      lengthReadout LengthUnit.meters setup.layerRiseh) ^ 2 +
                  lengthReadout LengthUnit.meters
                      setup.sourceDetectorSeparationD ^ 2) := by
          apply Real.sqrt_lt_sqrt
          · positivity
          · nlinarith
        linarith
    | D =>
        rfl

end PhyXMiniProblems.ProblemPhyXMini0329
