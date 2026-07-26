import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0559

open Dimension

/-!
# Volume of an obliquely oriented relativistic box

A rectangular box is at rest in the primed inertial frame `S'`.  Its three
proper edge lengths are `a' = 2 m`, `b' = 2 m`, and `c' = 4 m`.  The supplied
figure shows the primed coordinate axes, the three edge labels, and a
`25°` orientation marker.  Frame `S'` moves at the dimensionless speed
`β = 0.65` relative to the laboratory frame `S`.

Lengths and volumes below are unit-independent Physlib quantities.  Real
numbers occur only as named unit readouts, the dimensionless speed `β`, the
degree-valued orientation readout, and displayed answer values.

Assumption/target split:

* `MatchesRectangularBoxScenario` records the rest/laboratory frame roles and
  the simultaneous laboratory volume-measurement protocol;
* `MatchesSuppliedBoxFigure` records the visible `x'`, `y'`, `z'`, `S'`,
  `a'`, `b'`, `c'`, blue box, and `25°` orientation marker;
* `MatchesProblemReadouts` records the three proper lengths and `β = 0.65`;
* `SatisfiesRectangularBoxVolumeGeometry` states the generic rectangular-box
  product law in every length unit;
* `SatisfiesSpecialRelativisticVolumeContraction` states the generic law
  `V_S = V_S' / γ(β)` for a simultaneous spatial slice in `S`; and
* the values `16 m³`, `(4/5) √231 m³`, and agreement with `12.2 m³` occur only
  in the theorem conclusion.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout used for the three proper edge lengths. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Cubic-metre readout used for both requested volumes and the choices. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-! ## Frames, box geometry, and primary-figure vocabulary -/

/-- The laboratory frame and the box's proper rest frame. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- The three proper edge labels printed beside the box. -/
inductive ProperEdgeLabel where
  | aPrime
  | bPrime
  | cPrime
  deriving DecidableEq, Fintype, Repr

/-- The primed Cartesian axes visible in the supplied raster. -/
inductive PrimedCoordinateAxis where
  | xPrime
  | yPrime
  | zPrime
  deriving DecidableEq, Fintype, Repr

/-- Direction selected for the standard relative boost. -/
inductive BoostDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Protocol used to assign a three-dimensional volume in an inertial frame. -/
inductive VolumeMeasurementProtocol where
  | simultaneousSpatialSlice
  deriving DecidableEq, Repr

/-!
Qualitative and scalar information transcribed from
`phyx_data/test_image/559.png`.  The angle is a dimensionless degree readout;
the actual physical edge lengths and volumes are stored in the setup below.
-/
structure RelativisticBoxFigure where
  axisVisible : PrimedCoordinateAxis → Bool
  edgeLabelVisible : ProperEdgeLabel → Bool
  primedFrameLabelVisible : Bool
  boxDrawnAsRectangularParallelepiped : Bool
  boxShadedBlue : Bool
  orientationMarkerVisible : Bool
  orientationReferenceAxis : PrimedCoordinateAxis
  markedOrientationDegrees : ℝ

/-!
The physical box and its independent observables.  In particular,
`laboratoryVolume` is not defined from the contraction formula or an answer
choice; it is constrained only by the governing-law hypothesis below.
-/
structure RelativisticRectangularBoxSetup where
  figure : RelativisticBoxFigure
  laboratoryFrame : InertialFrameLabel
  boxRestFrame : InertialFrameLabel
  boostDirection : BoostDirection
  laboratoryVolumeProtocol : VolumeMeasurementProtocol
  properEdgeLength : ProperEdgeLabel → LengthQuantity
  restFrameVolume : VolumeQuantity
  laboratoryVolume : VolumeQuantity
  speedFractionOfLight : ℝ
  orientationDegreesInRestFrame : ℝ

/-- Physlib's Lorentz factor for the stated dimensionless relative speed. -/
def lorentzFactor (setup : RelativisticRectangularBoxSetup) : ℝ :=
  LorentzGroup.γ setup.speedFractionOfLight

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- The box is at rest in `S'`, while its volume in `S` is measured at one lab time. -/
structure MatchesRectangularBoxScenario
    (setup : RelativisticRectangularBoxSetup) : Prop where
  laboratoryFrameIsS : setup.laboratoryFrame = .S
  properFrameIsSPrime : setup.boxRestFrame = .SPrime
  motionAlongPositiveX : setup.boostDirection = .positiveX
  laboratoryMeasurementIsSimultaneous :
    setup.laboratoryVolumeProtocol = .simultaneousSpatialSlice

/-!
Primary-image evidence: all three primed axes and edge labels are visible,
the blue solid is rectangular, `S'` labels the primed frame, and the marked
orientation relative to `x'` is `25°`.
-/
structure MatchesSuppliedBoxFigure
    (setup : RelativisticRectangularBoxSetup) : Prop where
  everyPrimedAxisVisible : ∀ axis, setup.figure.axisVisible axis = true
  everyProperEdgeLabelVisible :
    ∀ edge, setup.figure.edgeLabelVisible edge = true
  primedFrameLabelShown : setup.figure.primedFrameLabelVisible = true
  rectangularParallelepipedShown :
    setup.figure.boxDrawnAsRectangularParallelepiped = true
  blueShadingShown : setup.figure.boxShadedBlue = true
  orientationMarkerShown : setup.figure.orientationMarkerVisible = true
  orientationMeasuredFromXPrime :
    setup.figure.orientationReferenceAxis = .xPrime
  figureAngleIsTwentyFiveDegrees :
    setup.figure.markedOrientationDegrees = 25
  setupOrientationMatchesFigure :
    setup.orientationDegreesInRestFrame =
      setup.figure.markedOrientationDegrees

/-!
Numerical data supplied by the prose.  These fields mention neither requested
volume nor any answer choice.
-/
structure MatchesProblemReadouts
    (setup : RelativisticRectangularBoxSetup) : Prop where
  edgeAPrimeMeters :
    lengthInMeters (setup.properEdgeLength .aPrime) = 2
  edgeBPrimeMeters :
    lengthInMeters (setup.properEdgeLength .bPrime) = 2
  edgeCPrimeMeters :
    lengthInMeters (setup.properEdgeLength .cPrime) = 4
  betaIsPointSixFive :
    setup.speedFractionOfLight = (13 / 20 : ℝ)

/-- Positivity of the box observables and the physical subluminal regime. -/
structure HasPhysicalRelativisticBoxParameters
    (setup : RelativisticRectangularBoxSetup) : Prop where
  everyProperEdgePositive :
    ∀ edge, 0 < lengthInMeters (setup.properEdgeLength edge)
  restFrameVolumePositive :
    0 < volumeInCubicMeters setup.restFrameVolume
  laboratoryVolumePositive :
    0 < volumeInCubicMeters setup.laboratoryVolume
  betaNonnegative : 0 ≤ setup.speedFractionOfLight
  betaSubluminal : setup.speedFractionOfLight < 1

/-!
Euclidean volume of a rectangular box is the product of its three mutually
orthogonal proper edge lengths.  Stating this in every unit keeps it a generic
geometry law rather than a problem-specific numerical answer.
-/
structure SatisfiesRectangularBoxVolumeGeometry
    (setup : RelativisticRectangularBoxSetup) : Prop where
  restVolumeProductLaw : ∀ unit : LengthUnit,
    volumeReadout unit setup.restFrameVolume =
      lengthReadout unit (setup.properEdgeLength .aPrime) *
        lengthReadout unit (setup.properEdgeLength .bPrime) *
          lengthReadout unit (setup.properEdgeLength .cPrime)

/-!
For a volume obtained from one simultaneity slice in the laboratory frame,
the determinant of the spatial Lorentz contraction gives
`V_S = V_S' / γ(β)`.  This generic law is independent of the box's rest-frame
orientation and contains no problem-specific volume value.
-/
structure SatisfiesSpecialRelativisticVolumeContraction
    (setup : RelativisticRectangularBoxSetup) : Prop where
  volumeContractionLaw : ∀ unit : LengthUnit,
    volumeReadout unit setup.laboratoryVolume =
      volumeReadout unit setup.restFrameVolume / lorentzFactor setup

/-! ## Multiple-choice target -/

/-- Labels of the four volume choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed cubic-metre value beside each answer label. -/
def displayedVolumeCubicMeters : AnswerChoice → ℝ
  | .A => 93 / 5
  | .B => 217 / 10
  | .C => 77 / 5
  | .D => 61 / 5

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a volume printed to one decimal place. -/
def AgreesWhenRoundedToOneDecimal
    (volumeCubicMeters : ℝ) (choice : AnswerChoice) : Prop :=
  |volumeCubicMeters - displayedVolumeCubicMeters choice| ≤ (1 / 20 : ℝ)

/-- A choice is at least as close to the computed lab volume as every alternative. -/
def IsNearestAnswerChoice
    (volumeCubicMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |volumeCubicMeters - displayedVolumeCubicMeters choice| ≤
      |volumeCubicMeters - displayedVolumeCubicMeters other|

/-!
The rest-frame volume is `2 · 2 · 4 = 16 m³`.  At `β = 13/20`, the laboratory
volume is

`16 / γ(13/20) = (4/5) √231 m³ ≈ 12.1586 m³`,

which rounds to `12.2 m³`, choice D.  The figure's `25°` orientation remains
part of the setup even though the volume-contraction determinant is independent
of that orientation.

Blueprint: `thm:physics:phyx_mini_0559:target`.
-/
theorem boxVolumesInRestAndLaboratoryFrames
    (setup : RelativisticRectangularBoxSetup)
    (hScenario : MatchesRectangularBoxScenario setup)
    (hFigure : MatchesSuppliedBoxFigure setup)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalRelativisticBoxParameters setup)
    (hGeometry : SatisfiesRectangularBoxVolumeGeometry setup)
    (hContraction : SatisfiesSpecialRelativisticVolumeContraction setup) :
    volumeInCubicMeters setup.restFrameVolume = 16 ∧
      volumeInCubicMeters setup.laboratoryVolume =
        (4 / 5 : ℝ) * Real.sqrt 231 ∧
      AgreesWhenRoundedToOneDecimal
        (volumeInCubicMeters setup.laboratoryVolume) .D ∧
      IsNearestAnswerChoice
        (volumeInCubicMeters setup.laboratoryVolume) .D := by
  have hRest : volumeInCubicMeters setup.restFrameVolume = 16 := by
    rw [volumeInCubicMeters,
      hGeometry.restVolumeProductLaw LengthUnit.meters]
    change
      lengthInMeters (setup.properEdgeLength .aPrime) *
        lengthInMeters (setup.properEdgeLength .bPrime) *
          lengthInMeters (setup.properEdgeLength .cPrime) = 16
    rw [hData.edgeAPrimeMeters, hData.edgeBPrimeMeters,
      hData.edgeCPrimeMeters]
    norm_num
  have hLab : volumeInCubicMeters setup.laboratoryVolume =
      (4 / 5 : ℝ) * Real.sqrt 231 := by
    calc
      volumeInCubicMeters setup.laboratoryVolume =
          volumeInCubicMeters setup.restFrameVolume / lorentzFactor setup := by
        simpa [volumeInCubicMeters] using
          hContraction.volumeContractionLaw LengthUnit.meters
      _ = 16 / LorentzGroup.γ (13 / 20 : ℝ) := by
        rw [hRest, lorentzFactor, hData.betaIsPointSixFive]
      _ = (4 / 5 : ℝ) * Real.sqrt 231 := by
        rw [LorentzGroup.γ]
        norm_num [div_div]
        field_simp <;> norm_num
  have hsqrtSq : (Real.sqrt 231) ^ 2 = (231 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 231 := Real.sqrt_nonneg 231
  have hsqrtLower : (243 / 16 : ℝ) ≤ Real.sqrt 231 := by
    nlinarith [hsqrtSq]
  have hsqrtUpper : Real.sqrt 231 ≤ (61 / 4 : ℝ) := by
    nlinarith [hsqrtSq]
  have hComputedLower : (243 / 20 : ℝ) ≤
      (4 / 5 : ℝ) * Real.sqrt 231 := by
    nlinarith [hsqrtLower]
  have hComputedUpper : (4 / 5 : ℝ) * Real.sqrt 231 ≤
      (61 / 5 : ℝ) := by
    nlinarith [hsqrtUpper]
  refine ⟨hRest, hLab, ?_, ?_⟩
  · rw [hLab]
    rw [AgreesWhenRoundedToOneDecimal, displayedVolumeCubicMeters, abs_le]
    constructor <;> nlinarith [hComputedLower, hComputedUpper]
  · rw [hLab]
    intro other
    have hDsign : (4 / 5 : ℝ) * Real.sqrt 231 - 61 / 5 ≤ 0 := by
      nlinarith [hComputedUpper]
    have hAsign : (4 / 5 : ℝ) * Real.sqrt 231 - 93 / 5 ≤ 0 := by
      nlinarith [hComputedUpper]
    have hBsign : (4 / 5 : ℝ) * Real.sqrt 231 - 217 / 10 ≤ 0 := by
      nlinarith [hComputedUpper]
    have hCsign : (4 / 5 : ℝ) * Real.sqrt 231 - 77 / 5 ≤ 0 := by
      nlinarith [hComputedUpper]
    cases other <;>
      simp [displayedVolumeCubicMeters,
        abs_of_nonpos hDsign, abs_of_nonpos hAsign,
        abs_of_nonpos hBsign, abs_of_nonpos hCsign] <;>
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0559
