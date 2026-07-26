import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0530

open Dimension

/-!
# Two successive Compton scatterings

An incident photon of wavelength `λ` scatters from a free electron at the
figure point `A`. The resulting photon of wavelength `λ'` scatters from a
second free electron at `B`, producing a photon of wavelength `λ''` traveling
opposite to the incident photon. The requested observable is the net
wavelength change `λ'' - λ`.

Wavelengths are unit-independent Physlib length quantities. Propagation and
recoil directions are vectors in the Euclidean plane. Bare real numbers are
used only for angles, named-unit readouts, and displayed answer values.
-/

/-! ## Physical quantities and geometric readouts -/

/-- A nonnegative, unit-independent physical wavelength or other length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A direction vector in the plane of the scattering diagram. -/
abbrev Direction2D : Type := EuclideanSpace ℝ (Fin 2)

/-- Read a physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical wavelength in picometers (`10⁻¹² m`). -/
def lengthInPicometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.picometers length

/-- The undirected angle, in radians, between two propagation directions. -/
def directionAngle (first second : Direction2D) : ℝ :=
  InnerProductGeometry.angle first second

/-! ## Labels and figure-derived roles -/

/-- The two interaction points labeled in the primary figure. -/
inductive InteractionPoint where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The three photon paths labeled by their wavelengths in the figure. -/
inductive PhotonLabel where
  | lambda
  | lambdaPrime
  | lambdaDoublePrime
  deriving DecidableEq, Fintype, Repr

/-- The two recoil electrons explicitly labeled in the figure. -/
inductive ElectronLabel where
  | electron1
  | electron2
  deriving DecidableEq, Fintype, Repr

/-- The three angle annotations printed in the primary figure. -/
inductive FigureAngleLabel where
  | alpha
  | theta
  | beta
  deriving DecidableEq, Fintype, Repr

/-- A photon state retains both its physical wavelength and propagation direction. -/
structure PhotonState where
  wavelength : LengthQuantity
  propagationDirection : Direction2D

/-!
Qualitative information visibly present in the supplied diagram. The
incidence maps say that `λ` enters `A`, `λ'` leaves `A` and enters `B`, and
`λ''` leaves `B`; they assign no numerical wavelength.
-/
structure SequentialComptonFigure where
  showsInteractionPoint : InteractionPoint → Bool
  showsPhotonLabel : PhotonLabel → Bool
  showsElectronLabel : ElectronLabel → Bool
  showsAngleLabel : FigureAngleLabel → Bool
  incidentPhotonAt : InteractionPoint → PhotonLabel
  outgoingPhotonAt : InteractionPoint → PhotonLabel
  recoilElectronAt : InteractionPoint → ElectronLabel
  initialPhotonDrawnRightward : Bool
  intermediatePhotonDrawnDownAndRight : Bool
  finalPhotonDrawnLeftward : Bool

/-!
Independent physical quantities for the two-stage event. In particular, the
three photon wavelengths are independent fields rather than definitions from
the requested net shift or from an answer choice.
-/
structure SequentialComptonSetup where
  photon : PhotonLabel → PhotonState
  electronRecoilDirection : ElectronLabel → Direction2D
  electronInitiallyFree : ElectronLabel → Prop
  electronInitiallyAtRest : ElectronLabel → Prop
  electronComptonWavelength : LengthQuantity
  figureAngleRadians : FigureAngleLabel → ℝ
  figure : SequentialComptonFigure

/-! ## Scenario, figure readouts, and physical laws -/

/-- The photon and electron roles at the two pictured interaction points. -/
structure MatchesSequentialScatteringScenario
    (setup : SequentialComptonSetup) : Prop where
  lambdaEntersA : setup.figure.incidentPhotonAt .A = .lambda
  lambdaPrimeLeavesA : setup.figure.outgoingPhotonAt .A = .lambdaPrime
  electron1RecoilsAtA : setup.figure.recoilElectronAt .A = .electron1
  lambdaPrimeEntersB : setup.figure.incidentPhotonAt .B = .lambdaPrime
  lambdaDoublePrimeLeavesB :
    setup.figure.outgoingPhotonAt .B = .lambdaDoublePrime
  electron2RecoilsAtB : setup.figure.recoilElectronAt .B = .electron2
  electron1IsInitiallyFree : setup.electronInitiallyFree .electron1
  electron2IsInitiallyFree : setup.electronInitiallyFree .electron2
  electron1IsInitiallyAtRest : setup.electronInitiallyAtRest .electron1
  electron2IsInitiallyAtRest : setup.electronInitiallyAtRest .electron2

/-!
Facts read from the primary image. The final photon is antiparallel to the
initial photon. The angle `θ` is between the initial and intermediate photon
paths, while `α` is the first recoil angle. In the image, `β` lies between the
continued intermediate path and Electron 2's recoil path.
-/
structure MatchesSequentialComptonFigure
    (setup : SequentialComptonSetup) : Prop where
  showsBothPoints : ∀ point, setup.figure.showsInteractionPoint point = true
  showsAllPhotonLabels : ∀ label, setup.figure.showsPhotonLabel label = true
  showsBothElectrons : ∀ electron, setup.figure.showsElectronLabel electron = true
  showsAllAngleLabels : ∀ angle, setup.figure.showsAngleLabel angle = true
  initialPathPointsRight : setup.figure.initialPhotonDrawnRightward = true
  intermediatePathPointsDownRight :
    setup.figure.intermediatePhotonDrawnDownAndRight = true
  finalPathPointsLeft : setup.figure.finalPhotonDrawnLeftward = true
  finalPhotonOpposesInitial :
    (setup.photon .lambdaDoublePrime).propagationDirection =
      -(setup.photon .lambda).propagationDirection
  alphaReadout :
    setup.figureAngleRadians .alpha =
      directionAngle
        (setup.photon .lambda).propagationDirection
        (setup.electronRecoilDirection .electron1)
  thetaReadout :
    setup.figureAngleRadians .theta =
      directionAngle
        (setup.photon .lambda).propagationDirection
        (setup.photon .lambdaPrime).propagationDirection
  betaReadout :
    setup.figureAngleRadians .beta =
      directionAngle
        (setup.photon .lambdaPrime).propagationDirection
        (setup.electronRecoilDirection .electron2)

/-!
Positivity and nondegeneracy conditions ensure every photon has a genuine
wavelength and direction and both electron recoil directions are meaningful.
-/
structure HasPhysicalSequentialComptonParameters
    (setup : SequentialComptonSetup) : Prop where
  photonWavelengthPositive :
    ∀ label unit, 0 < lengthReadout unit (setup.photon label).wavelength
  electronComptonWavelengthPositive :
    ∀ unit, 0 < lengthReadout unit setup.electronComptonWavelength
  photonDirectionNonzero :
    ∀ label, (setup.photon label).propagationDirection ≠ 0
  electronRecoilDirectionNonzero :
    ∀ electron, setup.electronRecoilDirection electron ≠ 0

/-!
The standard electron Compton wavelength, calibrated in picometers. The value
`2.42631 pm` is independent physical reference data, not the requested
two-scattering shift or an answer choice.
-/
def MatchesElectronComptonWavelengthReadout
    (setup : SequentialComptonSetup) : Prop :=
  lengthInPicometers setup.electronComptonWavelength = 242631 / 100000

/-!
The governing Compton law at each interaction. For an initially stationary
free electron, the outgoing photon wavelength exceeds the incoming one by
`λ_C (1 - cos φ)`, where `φ` is the angle between the photon paths. These are
two local laws; neither field states the requested total shift.
-/
structure SatisfiesTwoStageComptonScatteringLaws
    (setup : SequentialComptonSetup) : Prop where
  shiftAtA : ∀ unit : LengthUnit,
    lengthReadout unit (setup.photon .lambdaPrime).wavelength -
        lengthReadout unit (setup.photon .lambda).wavelength =
      lengthReadout unit setup.electronComptonWavelength *
        (1 - Real.cos
          (directionAngle
            (setup.photon .lambda).propagationDirection
            (setup.photon .lambdaPrime).propagationDirection))
  shiftAtB : ∀ unit : LengthUnit,
    lengthReadout unit (setup.photon .lambdaDoublePrime).wavelength -
        lengthReadout unit (setup.photon .lambdaPrime).wavelength =
      lengthReadout unit setup.electronComptonWavelength *
        (1 - Real.cos
          (directionAngle
            (setup.photon .lambdaPrime).propagationDirection
            (setup.photon .lambdaDoublePrime).propagationDirection))

/-!
Because the last photon is opposite the first, the two undirected photon
scattering angles are supplementary. This is a consequence of the figure,
not an answer-value premise.
-/
lemma photonScatteringAnglesAreSupplementary
    (setup : SequentialComptonSetup)
    (hPhysical : HasPhysicalSequentialComptonParameters setup)
    (hFigure : MatchesSequentialComptonFigure setup) :
    directionAngle
          (setup.photon .lambda).propagationDirection
          (setup.photon .lambdaPrime).propagationDirection +
        directionAngle
          (setup.photon .lambdaPrime).propagationDirection
          (setup.photon .lambdaDoublePrime).propagationDirection =
      Real.pi := by
  simp only [directionAngle, hFigure.finalPhotonOpposesInitial,
    InnerProductGeometry.angle_neg_right, InnerProductGeometry.angle_comm]
  ring

/-! ## Net shift, choices, and target -/

/-- The requested scalar `Δλ = λ'' - λ`, read in picometers. -/
def wavelengthShiftInPicometers (setup : SequentialComptonSetup) : ℝ :=
  lengthInPicometers (setup.photon .lambdaDoublePrime).wavelength -
    lengthInPicometers (setup.photon .lambda).wavelength

/-!
The local Compton laws and supplementary-angle geometry make the net shift
exactly twice the electron Compton wavelength. No calibration or answer choice
is used in this structural relation.
-/
lemma totalShiftEqualsTwiceElectronComptonWavelength
    (setup : SequentialComptonSetup)
    (hPhysical : HasPhysicalSequentialComptonParameters setup)
    (hFigure : MatchesSequentialComptonFigure setup)
    (hCompton : SatisfiesTwoStageComptonScatteringLaws setup) :
    wavelengthShiftInPicometers setup =
      2 * lengthInPicometers setup.electronComptonWavelength := by
  have hAngles :=
    photonScatteringAnglesAreSupplementary setup hPhysical hFigure
  have hSecondAngle :
      directionAngle
            (setup.photon .lambdaPrime).propagationDirection
            (setup.photon .lambdaDoublePrime).propagationDirection =
        Real.pi -
          directionAngle
            (setup.photon .lambda).propagationDirection
            (setup.photon .lambdaPrime).propagationDirection := by
    linarith
  have hCos :
      Real.cos
            (directionAngle
              (setup.photon .lambdaPrime).propagationDirection
              (setup.photon .lambdaDoublePrime).propagationDirection) =
        -Real.cos
          (directionAngle
            (setup.photon .lambda).propagationDirection
            (setup.photon .lambdaPrime).propagationDirection) := by
    rw [hSecondAngle, Real.cos_pi_sub]
  have hA := hCompton.shiftAtA LengthUnit.picometers
  have hB := hCompton.shiftAtB LengthUnit.picometers
  rw [hCos] at hB
  unfold wavelengthShiftInPicometers lengthInPicometers
  linarith

/-- Labels of the four wavelength-shift choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Picometer value printed beside each answer label (`1 pm = 10⁻¹² m`). -/
def displayedShiftInPicometers : AnswerChoice → ℝ
  | .A => 215 / 100
  | .B => 366 / 100
  | .C => 472 / 100
  | .D => 485 / 100

/-- Answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a picometer value displayed to the nearest `0.01 pm`. -/
def RoundsToNearestHundredthPicometer (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- A displayed choice agrees with the modeled net wavelength shift. -/
def MatchesAnswerChoice
    (setup : SequentialComptonSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthPicometer
    (wavelengthShiftInPicometers setup)
    (displayedShiftInPicometers choice)

/-!
The exact model gives `2 λ_C = 4.85262 pm`; hence the value rounds to
`4.85 pm = 4.85 × 10⁻¹² m`, and D is the unique matching displayed choice.

This formalizes `thm:physics:phyx_mini_0530:target`.
-/
theorem problem_phyx_mini_0530
    (setup : SequentialComptonSetup)
    (hScenario : MatchesSequentialScatteringScenario setup)
    (hFigure : MatchesSequentialComptonFigure setup)
    (hPhysical : HasPhysicalSequentialComptonParameters setup)
    (hReference : MatchesElectronComptonWavelengthReadout setup)
    (hCompton : SatisfiesTwoStageComptonScatteringLaws setup) :
    wavelengthShiftInPicometers setup = (242631 / 50000 : ℝ) ∧
      MatchesAnswerChoice setup .D ∧
      ∀ choice : AnswerChoice,
        MatchesAnswerChoice setup choice → choice = .D := by
  have hShift :=
    totalShiftEqualsTwiceElectronComptonWavelength
      setup hPhysical hFigure hCompton
  have hValue :
      wavelengthShiftInPicometers setup = (242631 / 50000 : ℝ) := by
    rw [hShift, hReference]
    norm_num
  refine ⟨hValue, ?_, ?_⟩
  · unfold MatchesAnswerChoice RoundsToNearestHundredthPicometer
    rw [hValue]
    norm_num [displayedShiftInPicometers, abs_of_nonneg]
  · intro choice hChoice
    cases choice <;>
      simp only [MatchesAnswerChoice, RoundsToNearestHundredthPicometer,
        displayedShiftInPicometers, hValue] at hChoice ⊢ <;>
      norm_num [abs_of_nonneg, abs_of_nonpos] at hChoice

end PhyXMiniProblems.ProblemPhyXMini0530
