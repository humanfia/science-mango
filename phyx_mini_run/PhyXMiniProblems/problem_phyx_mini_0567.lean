import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0567

open Dimension

/-!
# Speed of a nearby star from a two-percent wavelength blueshift

Light from a nearby star has fractional wavelength change
`Δλ / λ_emitted = -0.02`. The physical model below distinguishes the
emitted wavelength in the star frame, the observed wavelength in the Earth
observer frame, the signed wavelength change, and the nonnegative radial
speed of the star relative to that observer.

The supplied raster is not a stellar spectrum: it is an auxiliary two-panel
muon/Earth reference-frame diagram. Its labels and qualitative geometry are
retained explicitly, but it supplies no numerical Doppler datum.

Wavelengths, wavelength changes, and speed are unit-independent Physlib
quantities. Real numbers occur only at named-unit readout boundaries and for
dimensionless ratios and displayed answer values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical wavelength, carrying length dimension. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical wavelength change `Δλ`. -/
abbrev SignedWavelengthChangeQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical radial speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a wavelength in a selected unit of length. -/
def wavelengthReadout
    (unit : LengthUnit) (wavelength : WavelengthQuantity) : ℝ :=
  ((wavelength {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read the signed wavelength change in a selected unit of length. -/
def signedWavelengthChangeReadout
    (unit : LengthUnit) (change : SignedWavelengthChangeQuantity) : ℝ :=
  (change {UnitChoices.SI with length := unit}).val

/-- Read a speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read Physlib's dimensionful vacuum speed of light in compatible units. -/
def vacuumLightSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-! ## Stellar source, observer, and wavelength roles -/

/-- The astronomical source classification stated in the problem. -/
inductive AstronomicalSourceKind where
  | nearbyStar
  | other
  deriving DecidableEq, Repr

/-- The observing location relative to which the radial motion is measured. -/
inductive ObserverLocation where
  | earth
  | other
  deriving DecidableEq, Repr

/-- The light observable whose displacement is measured spectroscopically. -/
inductive LightSignalKind where
  | stellarSpectralLine
  | other
  deriving DecidableEq, Repr

/-- The two inertial frames used for emission and observation. -/
inductive DopplerFrame where
  | starRestFrame
  | earthObserverFrame
  deriving DecidableEq, Repr

/-- Direction of the star's radial motion in the observer's convention. -/
inductive RadialMotion where
  | towardObserver
  | awayFromObserver
  | transverse
  deriving DecidableEq, Repr

/-! ## Auxiliary muon/Earth raster data -/

/-- The left and right panels in the supplied auxiliary image. -/
inductive AuxiliaryFigurePanel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two reference frames labelled by the image origins `O_mu` and `O_e`. -/
inductive AuxiliaryReferenceFrame where
  | muonFrame
  | earthFrame
  deriving DecidableEq, Fintype, Repr

/-- Literal coordinate-axis labels visible in the image. -/
inductive AuxiliaryAxisLabel where
  | xMuon
  | yMuon
  | xEarth
  | yEarth
  deriving DecidableEq, Fintype, Repr

/-- Origin labels visible in the image. -/
inductive AuxiliaryOriginLabel where
  | OMuon
  | OEarth
  deriving DecidableEq, Fintype, Repr

/-- Physical objects drawn in both panels. -/
inductive AuxiliaryFigureObject where
  | muon
  | earth
  | observer
  deriving DecidableEq, Fintype, Repr

/-- Glyph styles used to distinguish the three objects in the raster. -/
inductive AuxiliaryObjectGlyph where
  | redCircle
  | horizontalSurface
  | redStickFigure
  deriving DecidableEq, Fintype, Repr

/-- Vertical direction of each arrow labelled `V`. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The opposite-axis convention printed at the top of either panel. -/
inductive VerticalCoordinateRelation where
  | yEarthEqualsNegativeYMuon
  | yMuonEqualsNegativeYEarth
  deriving DecidableEq, Repr

/-!
Qualitative and literal information transcribed from image 567. The image
has no quantitative spatial scale and no stellar wavelength or speed label.
-/
structure MuonEarthReferenceFrameFigure where
  topFrame : AuxiliaryFigurePanel → AuxiliaryReferenceFrame
  bottomOrigin : AuxiliaryFigurePanel → AuxiliaryOriginLabel
  axisLabelShown : AuxiliaryFigurePanel → AuxiliaryAxisLabel → Bool
  objectShown : AuxiliaryFigurePanel → AuxiliaryFigureObject → Bool
  objectGlyph : AuxiliaryFigureObject → AuxiliaryObjectGlyph
  velocityArrowAttachedTo : AuxiliaryFigurePanel → AuxiliaryFigureObject
  velocityArrowDirection : AuxiliaryFigurePanel → VerticalDirection
  velocityLabelVShown : AuxiliaryFigurePanel → Bool
  verticalCoordinateRelation :
    AuxiliaryFigurePanel → VerticalCoordinateRelation
  hasQuantitativeSpatialScale : Bool
  hasStellarDopplerReadout : Bool

/-!
Primary-image evidence. The left panel is organized around `O_mu`, with
`x_mu`, `y_mu`, and `x_e` shown and the muon's `V` arrow downward. The right
panel is organized around `O_e`, with `x_e`, `y_e`, and `x_mu` shown and the
Earth's `V` arrow downward. The displayed coordinate conventions are
`y_e ≡ -y_mu` and `y_mu ≡ -y_e` respectively.
-/
structure MatchesSuppliedAuxiliaryFigure
    (figure : MuonEarthReferenceFrameFigure) : Prop where
  leftTopFrame : figure.topFrame .left = .muonFrame
  rightTopFrame : figure.topFrame .right = .earthFrame
  leftBottomOrigin : figure.bottomOrigin .left = .OEarth
  rightBottomOrigin : figure.bottomOrigin .right = .OMuon
  leftXMuonShown : figure.axisLabelShown .left .xMuon = true
  leftYMuonShown : figure.axisLabelShown .left .yMuon = true
  leftXEarthShown : figure.axisLabelShown .left .xEarth = true
  leftYEarthNotSeparatelyDrawn :
    figure.axisLabelShown .left .yEarth = false
  rightXEarthShown : figure.axisLabelShown .right .xEarth = true
  rightYEarthShown : figure.axisLabelShown .right .yEarth = true
  rightXMuonShown : figure.axisLabelShown .right .xMuon = true
  rightYMuonNotSeparatelyDrawn :
    figure.axisLabelShown .right .yMuon = false
  everyObjectShown : ∀ panel object,
    figure.objectShown panel object = true
  muonGlyph : figure.objectGlyph .muon = .redCircle
  earthGlyph : figure.objectGlyph .earth = .horizontalSurface
  observerGlyph : figure.objectGlyph .observer = .redStickFigure
  leftVelocityAttachedToMuon :
    figure.velocityArrowAttachedTo .left = .muon
  rightVelocityAttachedToEarth :
    figure.velocityArrowAttachedTo .right = .earth
  bothVelocityArrowsPointDown : ∀ panel,
    figure.velocityArrowDirection panel = .downward
  bothVelocityLabelsShown : ∀ panel,
    figure.velocityLabelVShown panel = true
  leftVerticalCoordinateConvention :
    figure.verticalCoordinateRelation .left =
      .yEarthEqualsNegativeYMuon
  rightVerticalCoordinateConvention :
    figure.verticalCoordinateRelation .right =
      .yMuonEqualsNegativeYEarth
  noQuantitativeSpatialScale :
    figure.hasQuantitativeSpatialScale = false
  noStellarDopplerReadout : figure.hasStellarDopplerReadout = false

/-! ## Independent stellar Doppler setup -/

/-!
The physical quantities and role assignments of the observation.
`starRadialSpeedRelativeToObserver` is independent data constrained only by
the Doppler law below; it is not defined from the recorded answer choice.
-/
structure StellarBlueshiftSetup where
  sourceKind : AstronomicalSourceKind
  observerLocation : ObserverLocation
  lightSignalKind : LightSignalKind
  emittedWavelengthFrame : DopplerFrame
  observedWavelengthFrame : DopplerFrame
  radialMotion : RadialMotion
  emittedWavelength : WavelengthQuantity
  observedWavelength : WavelengthQuantity
  wavelengthChangeDelta : SignedWavelengthChangeQuantity
  starRadialSpeedRelativeToObserver : SpeedQuantity
  auxiliaryFigure : MuonEarthReferenceFrameFigure

/-! The dimensionless speed ratio `β = v/c`, derived from physical speeds. -/
def speedFractionOfLight (setup : StellarBlueshiftSetup) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds
      setup.starRadialSpeedRelativeToObserver /
    vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds

/-!
The nearby stellar source, Earth observer, frame assignments, and approaching
radial direction stated or implied by a blueshift.
-/
structure MatchesStellarBlueshiftScenario
    (setup : StellarBlueshiftSetup) : Prop where
  nearbyStellarSource : setup.sourceKind = .nearbyStar
  earthBasedObserver : setup.observerLocation = .earth
  spectralLineMeasurement : setup.lightSignalKind = .stellarSpectralLine
  emissionMeasuredInStarFrame :
    setup.emittedWavelengthFrame = .starRestFrame
  observationMeasuredInEarthFrame :
    setup.observedWavelengthFrame = .earthObserverFrame
  starApproachesObserver : setup.radialMotion = .towardObserver

/-!
The literal problem readout `Δλ / λ = -0.02`. Here
`Δλ = λ_observed - λ_emitted`, and the denominator is the emitted rest
wavelength. The equations are imposed in every length unit to make their
dimensionless meaning explicit. No speed value occurs in these premises.
-/
structure MatchesTwoPercentWavelengthBlueshift
    (setup : StellarBlueshiftSetup) : Prop where
  wavelengthChangeIsObservedMinusEmitted : ∀ unit : LengthUnit,
    signedWavelengthChangeReadout unit setup.wavelengthChangeDelta =
      wavelengthReadout unit setup.observedWavelength -
        wavelengthReadout unit setup.emittedWavelength
  fractionalWavelengthShift : ∀ unit : LengthUnit,
    signedWavelengthChangeReadout unit setup.wavelengthChangeDelta /
        wavelengthReadout unit setup.emittedWavelength = -(1 / 50 : ℝ)

/-!
Positivity and the ordinary subluminal branch of the stellar observation.
These conditions select the physical branch of the square root but do not
assign a numerical value to the star's speed.
-/
structure HasPhysicalStellarDopplerParameters
    (setup : StellarBlueshiftSetup) : Prop where
  emittedWavelengthPositive : ∀ unit : LengthUnit,
    0 < wavelengthReadout unit setup.emittedWavelength
  observedWavelengthPositive : ∀ unit : LengthUnit,
    0 < wavelengthReadout unit setup.observedWavelength
  vacuumLightSpeedPositive :
    0 < vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds
  speedFractionNonnegative : 0 ≤ speedFractionOfLight setup
  speedFractionSubluminal : speedFractionOfLight setup < 1

/-!
The longitudinal relativistic Doppler law for an approaching source,

`λ_observed / λ_emitted = sqrt ((1 - β) / (1 + β))`.

This is a general governing relation between the independent wavelengths and
speed. It contains neither the problem-specific exact speed nor an answer
choice.
-/
structure SatisfiesApproachingSourceRelativisticDopplerLaw
    (setup : StellarBlueshiftSetup) : Prop where
  approachingWavelengthLaw : ∀ unit : LengthUnit,
    wavelengthReadout unit setup.observedWavelength /
        wavelengthReadout unit setup.emittedWavelength =
      Real.sqrt
        ((1 - speedFractionOfLight setup) /
          (1 + speedFractionOfLight setup))

/-! ## Displayed choices and requested speed -/

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The nonnegative coefficient of `c` printed beside each answer label. -/
def displayedSpeedFractionOfLight : AnswerChoice → ℝ
  | .A => 11 / 20
  | .B => 99 / 5000
  | .C => 19 / 20
  | .D => 51 / 5

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A displayed choice is selected by ordinary multiple-choice proximity to the
exact modeled speed fraction. This matters because the printed `0.0198 c`
is close to, but not equal to, the exact consequence of the written
wavelength shift.
-/
def IsClosestDisplayedSpeedChoice
    (setup : StellarBlueshiftSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |speedFractionOfLight setup - displayedSpeedFractionOfLight choice| <
      |speedFractionOfLight setup - displayedSpeedFractionOfLight other|

/-!
From `Δλ / λ_emitted = -1/50`, the observed-to-emitted wavelength ratio is
`49/50`. The relativistic Doppler law therefore gives

`β = (1 - (49/50)^2) / (1 + (49/50)^2) = 99/4901`.

Thus the dimensionful radial speed is `(99/4901)c`, approximately
`0.02020c`. Of the four printed alternatives, B (`0.0198c`) is uniquely
closest. The discrepancy is retained rather than replacing the stated
wavelength equation by a two-percent frequency increase.

This formalizes `thm:physics:phyx_mini_0567:target`.
-/
theorem problem_phyx_mini_0567
    (setup : StellarBlueshiftSetup)
    (hScenario : MatchesStellarBlueshiftScenario setup)
    (hReadout : MatchesTwoPercentWavelengthBlueshift setup)
    (hFigure : MatchesSuppliedAuxiliaryFigure setup.auxiliaryFigure)
    (hPhysical : HasPhysicalStellarDopplerParameters setup)
    (hDoppler :
      SatisfiesApproachingSourceRelativisticDopplerLaw setup) :
    speedFractionOfLight setup = 99 / 4901 ∧
      (∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        speedReadout lengthUnit timeUnit
            setup.starRadialSpeedRelativeToObserver =
          (99 / 4901 : ℝ) *
            vacuumLightSpeedReadout lengthUnit timeUnit) ∧
      IsClosestDisplayedSpeedChoice setup .B ∧
      ∀ choice : AnswerChoice,
        IsClosestDisplayedSpeedChoice setup choice → choice = .B := by
  have hEmittedPositive :
      0 < wavelengthReadout LengthUnit.meters setup.emittedWavelength :=
    hPhysical.emittedWavelengthPositive LengthUnit.meters
  have hEmittedNe :
      wavelengthReadout LengthUnit.meters setup.emittedWavelength ≠ 0 :=
    ne_of_gt hEmittedPositive
  have hChange :=
    hReadout.wavelengthChangeIsObservedMinusEmitted LengthUnit.meters
  have hShift :=
    hReadout.fractionalWavelengthShift LengthUnit.meters
  have hShiftMul :
      signedWavelengthChangeReadout LengthUnit.meters
          setup.wavelengthChangeDelta =
        (-(1 / 50 : ℝ)) *
          wavelengthReadout LengthUnit.meters setup.emittedWavelength :=
    (div_eq_iff hEmittedNe).mp hShift
  rw [hChange] at hShiftMul
  have hWavelengthRatio :
      wavelengthReadout LengthUnit.meters setup.observedWavelength /
          wavelengthReadout LengthUnit.meters setup.emittedWavelength =
        (49 / 50 : ℝ) := by
    apply (div_eq_iff hEmittedNe).2
    linarith
  have hDopplerMeters :=
    hDoppler.approachingWavelengthLaw LengthUnit.meters
  rw [hWavelengthRatio] at hDopplerMeters
  have hRadicandNonnegative :
      0 ≤
        (1 - speedFractionOfLight setup) /
          (1 + speedFractionOfLight setup) := by
    exact div_nonneg
      (sub_nonneg.mpr (le_of_lt hPhysical.speedFractionSubluminal))
      (by linarith [hPhysical.speedFractionNonnegative])
  have hSquaredDoppler :
      (49 / 50 : ℝ) ^ 2 =
        (1 - speedFractionOfLight setup) /
          (1 + speedFractionOfLight setup) := by
    calc
      (49 / 50 : ℝ) ^ 2 =
          (Real.sqrt
            ((1 - speedFractionOfLight setup) /
              (1 + speedFractionOfLight setup))) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hDopplerMeters
      _ = (1 - speedFractionOfLight setup) /
          (1 + speedFractionOfLight setup) :=
        Real.sq_sqrt hRadicandNonnegative
  have hDopplerDenominatorNe :
      1 + speedFractionOfLight setup ≠ 0 := by
    linarith [hPhysical.speedFractionNonnegative]
  have hBetaExact :
      speedFractionOfLight setup = (99 / 4901 : ℝ) := by
    rw [eq_div_iff hDopplerDenominatorNe] at hSquaredDoppler
    norm_num at hSquaredDoppler ⊢
    linarith
  have hSpeedSI :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.starRadialSpeedRelativeToObserver =
        (99 / 4901 : ℝ) *
          vacuumLightSpeedReadout LengthUnit.meters TimeUnit.seconds := by
    exact (div_eq_iff
      (ne_of_gt hPhysical.vacuumLightSpeedPositive)).mp
        (by simpa [speedFractionOfLight] using hBetaExact)
  have hReadoutRelation :
      ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
        speedReadout lengthUnit timeUnit
            setup.starRadialSpeedRelativeToObserver =
          (99 / 4901 : ℝ) *
            vacuumLightSpeedReadout lengthUnit timeUnit := by
    intro lengthUnit timeUnit
    let units : UnitChoices :=
      {UnitChoices.SI with
        length := lengthUnit, time := timeUnit}
    have hSpeedScaleRaw :=
      setup.starRadialSpeedRelativeToObserver.2 UnitChoices.SI units
    have hLightScaleRaw :=
      DimSpeed.speedOfLight.2 UnitChoices.SI units
    have hSpeedScale :
        speedReadout lengthUnit timeUnit
            setup.starRadialSpeedRelativeToObserver =
          (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            speedReadout LengthUnit.meters TimeUnit.seconds
              setup.starRadialSpeedRelativeToObserver := by
      simpa [speedReadout, units, UnitChoices.SI, NNReal.smul_def,
        smul_eq_mul] using
          congrArg (fun value => ((value.val : NNReal) : ℝ)) hSpeedScaleRaw
    have hLightScale :
        vacuumLightSpeedReadout lengthUnit timeUnit =
          (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            vacuumLightSpeedReadout
              LengthUnit.meters TimeUnit.seconds := by
      simpa [vacuumLightSpeedReadout, units, UnitChoices.SI,
        NNReal.smul_def, smul_eq_mul] using
          congrArg WithDim.val hLightScaleRaw
    calc
      speedReadout lengthUnit timeUnit
          setup.starRadialSpeedRelativeToObserver =
          (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            speedReadout LengthUnit.meters TimeUnit.seconds
              setup.starRadialSpeedRelativeToObserver := hSpeedScale
      _ = (UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
          ((99 / 4901 : ℝ) *
            vacuumLightSpeedReadout
              LengthUnit.meters TimeUnit.seconds) := by rw [hSpeedSI]
      _ = (99 / 4901 : ℝ) *
          ((UnitChoices.SI.dimScale units (L𝓭 * T𝓭⁻¹) : ℝ) *
            vacuumLightSpeedReadout
              LengthUnit.meters TimeUnit.seconds) := by ring
      _ = (99 / 4901 : ℝ) *
          vacuumLightSpeedReadout lengthUnit timeUnit := by
            rw [hLightScale]
  have hClosest :
      IsClosestDisplayedSpeedChoice setup .B := by
    intro other hOther
    rw [hBetaExact]
    fin_cases other
    · norm_num [displayedSpeedFractionOfLight, abs_of_nonneg, abs_of_nonpos]
    · simp at hOther
    · norm_num [displayedSpeedFractionOfLight, abs_of_nonneg, abs_of_nonpos]
    · norm_num [displayedSpeedFractionOfLight, abs_of_nonneg, abs_of_nonpos]
  refine ⟨hBetaExact, hReadoutRelation, hClosest, ?_⟩
  intro choice hChoice
  by_contra hChoiceNe
  have hBCloser := hClosest choice hChoiceNe
  have hChoiceCloser := hChoice .B (Ne.symm hChoiceNe)
  linarith

end PhyXMiniProblems.ProblemPhyXMini0567
