import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Electron energy in a two-dimensional infinite rectangular well

The primary image shows a rectangular well in the `xy`-plane, with side
labels `L_x` and `L_y` and dashed vertical and horizontal bisectors.  A probe
on the vertical line bisecting `L_x` reports three probability maxima separated
by `2.00 nm`; a probe on the horizontal line bisecting `L_y` reports five
maxima separated by `3.00 nm`.

Lengths, mass, action, and energy remain dimensionful physical quantities.
Real numbers below are only coherent-unit readouts, coordinates in the metre
chart, wavefunction values, dimensionless counts, or the literal symbolic
answer-choice expressions supplied by the dataset.

Assumption/target boundary:

* `MatchesPrimaryRectangularWellFigure` records only geometry and labels visible
  in the supplied raster.
* `MatchesDetectionProbeReadouts` records the two measured peak counts,
  spacings, and the fact that the reported points are all the maxima on their
  respective probe lines.
* `SatisfiesInfiniteRectangularWellLaws` states the general separable stationary
  mode, peak interpretation, and two-dimensional energy spectrum.
* `UsesElectronReferenceData` and `UsesStandardPlanckConstant` supply standard
  calibration data, not the requested energy.
* There are no previous-part results.  The quantum numbers, side lengths, and
  electron energy occur only as conclusions of the derived lemmas and theorem.

The dataset's recorded choice C is retained as source metadata.  Its four
one-parameter symbolic formulas do not contain both measured spacings and are
therefore not used as a premise for the two-dimensional energy calculation.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0584

open Dimension MeasureTheory

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action such as Planck's constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometre readout used for the supplied probe separations. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass ({UnitChoices.SI with mass := MassUnit.kilograms} : UnitChoices)).val : ℝ)

/-- Joule-second readout of a physical action. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Electron-volt readout grounded in Physlib's calibrated electron volt. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-! ## Plane, particle, probe, and primary-figure vocabulary -/

/-- The two coordinate axes of the rectangular well. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The `Fin 2` coordinate selected by an axis label. -/
def CoordinateAxis.toFin : CoordinateAxis → Fin 2
  | .x => 0
  | .y => 1

/-- Read one coordinate of a point in the coherent metre chart. -/
def coordinateInMeters (axis : CoordinateAxis) (point : Space 2) : ℝ :=
  point axis.toFin

/-- Particle species confined by the potential. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Spatial plane in which the well lies. -/
inductive SpatialPlane where
  | xy
  | other
  deriving DecidableEq, Repr

/-- Confinement idealization stated in the problem. -/
inductive ConfinementModel where
  | twoDimensionalInfiniteRectangularWell
  | other
  deriving DecidableEq, Repr

/-!
The two dashed probe lines.  `verticalBisectorOfLx` fixes `x = L_x/2` and
varies `y`; `horizontalBisectorOfLy` fixes `y = L_y/2` and varies `x`.
-/
inductive ProbeLine where
  | verticalBisectorOfLx
  | horizontalBisectorOfLy
  deriving DecidableEq, Fintype, Repr

/-- Coordinate that varies while moving along a probe line. -/
def ProbeLine.variedAxis : ProbeLine → CoordinateAxis
  | .verticalBisectorOfLx => .y
  | .horizontalBisectorOfLy => .x

/-- Coordinate fixed at half the corresponding side length. -/
def ProbeLine.bisectedAxis : ProbeLine → CoordinateAxis
  | .verticalBisectorOfLx => .x
  | .horizontalBisectorOfLy => .y

/-- Literal mathematical labels visible in the supplied raster. -/
inductive FigureLabel where
  | xAxis
  | yAxis
  | lengthLx
  | lengthLy
  deriving DecidableEq, Fintype, Repr

/-- Primary-image features of the rectangular well and its two bisectors. -/
structure RectangularWellFigure where
  showsLabel : FigureLabel → Bool
  boundaryIsRectangle : Bool
  boundaryIsBlue : Bool
  verticalBisectorIsDashed : Bool
  horizontalBisectorIsDashed : Bool
  horizontalSideLabel : FigureLabel
  verticalSideLabel : FigureLabel

/-!
A finite readout of all equal-height detection-probability maxima found on one
probe line.  The points use the coherent metre coordinate chart; their common
spacing remains a dimensionful length.
-/
structure DetectionProbeObservation where
  maximumCount : ℕ
  maximumPoint : Fin maximumCount → Space 2
  adjacentMaximumSpacing : LengthQuantity

/-!
Independent physical quantities for the confined electron.  In particular,
`stateEnergy`, quantum numbers, and side lengths are fields constrained by
general laws below; none is defined from the requested answer.
-/
structure RectangularWellElectronSetup where
  particleSpecies : ParticleSpecies
  spatialPlane : SpatialPlane
  confinementModel : ConfinementModel
  particleMass : MassQuantity
  ordinaryPlanckAction : ActionQuantity
  sideLength : CoordinateAxis → LengthQuantity
  quantumNumber : CoordinateAxis → ℕ
  stateEnergy : DimEnergy
  waveFunction : QuantumMechanics.SpaceDHilbertSpace 2
  waveRepresentative : Space 2 → ℂ
  probeObservation : ProbeLine → DetectionProbeObservation
  figure : RectangularWellFigure

/-! ## Geometry, probability density, and probe maxima -/

/-- A point lies in the closed rectangular well in the SI coordinate chart. -/
def IsInsideRectangularWell
    (setup : RectangularWellElectronSetup) (point : Space 2) : Prop :=
  0 ≤ coordinateInMeters .x point ∧
    coordinateInMeters .x point ≤ lengthInMeters (setup.sideLength .x) ∧
    0 ≤ coordinateInMeters .y point ∧
    coordinateInMeters .y point ≤ lengthInMeters (setup.sideLength .y)

/-- A point lies on the selected geometric bisector of the well. -/
def LiesOnProbeLine
    (setup : RectangularWellElectronSetup)
    (line : ProbeLine) (point : Space 2) : Prop :=
  coordinateInMeters line.bisectedAxis point =
    lengthInMeters (setup.sideLength line.bisectedAxis) / 2

/-- Pointwise detection-probability density of the chosen wave representative. -/
def detectionProbabilityDensity
    (setup : RectangularWellElectronSetup) (point : Space 2) : ℝ :=
  Complex.normSq (setup.waveRepresentative point)

/-- A global detection-probability maximum along one in-well probe segment. -/
def IsDetectionProbabilityMaximumAlong
    (setup : RectangularWellElectronSetup)
    (line : ProbeLine) (point : Space 2) : Prop :=
  IsInsideRectangularWell setup point ∧
    LiesOnProbeLine setup line point ∧
    ∀ other : Space 2,
      IsInsideRectangularWell setup other →
      LiesOnProbeLine setup line other →
      detectionProbabilityDensity setup other ≤
        detectionProbabilityDensity setup point

/-! ## Scenario facts, figure readouts, and reference data -/

/-- Categorical facts explicitly stated by the physical scenario. -/
structure MatchesRectangularWellElectronScenario
    (setup : RectangularWellElectronSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  wellLiesInXYPlane : setup.spatialPlane = .xy
  confinementIsTwoDimensionalInfiniteRectangle :
    setup.confinementModel = .twoDimensionalInfiniteRectangularWell

/-- Geometry and labels transcribed from the primary raster. -/
structure MatchesPrimaryRectangularWellFigure
    (figure : RectangularWellFigure) : Prop where
  everyPrintedLabelShown : ∀ label, figure.showsLabel label = true
  blueRectangularBoundary :
    figure.boundaryIsRectangle = true ∧ figure.boundaryIsBlue = true
  dashedVerticalBisector : figure.verticalBisectorIsDashed = true
  dashedHorizontalBisector : figure.horizontalBisectorIsDashed = true
  horizontalSideIsLx : figure.horizontalSideLabel = .lengthLx
  verticalSideIsLy : figure.verticalSideLabel = .lengthLy

/-!
The two experimental scan readouts.  Besides the stated counts and spacings,
the fields say that the listed points really are distinct maxima, exhaust all
maxima on the relevant line, occur with nonzero density, and are listed in
increasing order with the reported uniform adjacent separation.
-/
structure MatchesDetectionProbeReadouts
    (setup : RectangularWellElectronSetup) : Prop where
  verticalProbeHasThreeMaxima :
    (setup.probeObservation .verticalBisectorOfLx).maximumCount = 3
  verticalProbeSpacingIsTwoNanometers :
    lengthInNanometers
      (setup.probeObservation .verticalBisectorOfLx).adjacentMaximumSpacing = 2
  horizontalProbeHasFiveMaxima :
    (setup.probeObservation .horizontalBisectorOfLy).maximumCount = 5
  horizontalProbeSpacingIsThreeNanometers :
    lengthInNanometers
      (setup.probeObservation .horizontalBisectorOfLy).adjacentMaximumSpacing = 3
  reportedPointsAreDistinct :
    ∀ line : ProbeLine,
      Function.Injective (setup.probeObservation line).maximumPoint
  reportedPointsAreNonzeroMaxima :
    ∀ line : ProbeLine,
      ∀ i : Fin (setup.probeObservation line).maximumCount,
        IsDetectionProbabilityMaximumAlong setup line
          ((setup.probeObservation line).maximumPoint i) ∧
        0 < detectionProbabilityDensity setup
          ((setup.probeObservation line).maximumPoint i)
  everyMaximumWasReported :
    ∀ line : ProbeLine, ∀ point : Space 2,
      IsDetectionProbabilityMaximumAlong setup line point →
      ∃ i : Fin (setup.probeObservation line).maximumCount,
        point = (setup.probeObservation line).maximumPoint i
  adjacentPointsHaveReportedSpacing :
    ∀ line : ProbeLine,
      ∀ i j : Fin (setup.probeObservation line).maximumCount,
        i.val + 1 = j.val →
        coordinateInMeters line.variedAxis
            ((setup.probeObservation line).maximumPoint j) -
          coordinateInMeters line.variedAxis
            ((setup.probeObservation line).maximumPoint i) =
          lengthInMeters
            (setup.probeObservation line).adjacentMaximumSpacing

/-!
Reference mass needed for numerical evaluation.  No electron-mass constant
was found in the searched Physlib API, so the 2022 CODATA kilogram readout is
stated separately from the problem and figure observations.
-/
structure UsesElectronReferenceData
    (setup : RectangularWellElectronSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.particleMass = 9.1093837139e-31

/-!
Physlib supplies the reduced Planck constant `Constants.ℏ` in joule-seconds;
ordinary Planck action is `h = 2πℏ`.
-/
structure UsesStandardPlanckConstant
    (setup : RectangularWellElectronSetup) : Prop where
  ordinaryPlanckActionSI :
    actionInJouleSeconds setup.ordinaryPlanckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalRectangularWellParameters
    (setup : RectangularWellElectronSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.particleMass
  positivePlanckAction : 0 < actionInJouleSeconds setup.ordinaryPlanckAction
  positiveSideLengths :
    ∀ axis : CoordinateAxis, 0 < lengthInMeters (setup.sideLength axis)
  positiveQuantumNumbers :
    ∀ axis : CoordinateAxis, 0 < setup.quantumNumber axis
  positiveProbeSpacings :
    ∀ line : ProbeLine,
      0 < lengthInMeters
        (setup.probeObservation line).adjacentMaximumSpacing
  positiveEnergy : 0 < energyInJoules setup.stateEnergy

/-! ## Governing quantum-mechanical laws -/

/-!
The general stationary-state laws for a two-dimensional infinite rectangular
well.  The pointwise representative has the separable sine profile inside the
hard walls and vanishes outside.  Along a non-nodal bisector scan, the number
of equal maxima is the quantum number for the varying coordinate, adjacent
maxima are separated by `L/n`, and the spectrum is

`E_(n_x,n_y) = h^2/(8m) * (n_x^2/L_x^2 + n_y^2/L_y^2)`.

These are general relations involving the independent setup fields; they do
not contain the measured numbers `3`, `5`, `2 nm`, `3 nm`, or the requested
energy value.
-/
structure SatisfiesInfiniteRectangularWellLaws
    (setup : RectangularWellElectronSetup) : Prop where
  representativeIsSquareIntegrable :
    QuantumMechanics.SpaceDHilbertSpace.MemHS setup.waveRepresentative
  hilbertStateAgreesAlmostEverywhere :
    (setup.waveFunction : Space 2 → ℂ) =ᵐ[volume] setup.waveRepresentative
  separableSineProfileInside :
    ∃ amplitude : ℂ, amplitude ≠ 0 ∧
      ∀ point : Space 2,
        IsInsideRectangularWell setup point →
          setup.waveRepresentative point =
            amplitude *
                (Real.sin
                  ((setup.quantumNumber .x : ℝ) * Real.pi *
                    coordinateInMeters .x point /
                    lengthInMeters (setup.sideLength .x)) : ℂ) *
              (Real.sin
                ((setup.quantumNumber .y : ℝ) * Real.pi *
                  coordinateInMeters .y point /
                  lengthInMeters (setup.sideLength .y)) : ℂ)
  wavefunctionVanishesOutsideWell :
    ∀ point : Space 2,
      ¬ IsInsideRectangularWell setup point →
        setup.waveRepresentative point = 0
  quantumNumberCountsProbeMaxima :
    ∀ line : ProbeLine,
      setup.quantumNumber line.variedAxis =
        (setup.probeObservation line).maximumCount
  sideLengthEqualsPeakCountTimesSpacing :
    ∀ line : ProbeLine,
      lengthInMeters (setup.sideLength line.variedAxis) =
        ((setup.probeObservation line).maximumCount : ℝ) *
          lengthInMeters
            (setup.probeObservation line).adjacentMaximumSpacing
  twoDimensionalEnergySpectrum :
    energyInJoules setup.stateEnergy =
      actionInJouleSeconds setup.ordinaryPlanckAction ^ 2 /
        (8 * massInKilograms setup.particleMass) *
          ((setup.quantumNumber .x : ℝ) ^ 2 /
              lengthInMeters (setup.sideLength .x) ^ 2 +
            (setup.quantumNumber .y : ℝ) ^ 2 /
              lengthInMeters (setup.sideLength .y) ^ 2)

/-! ## Literal dataset answer-choice metadata -/

/-- The four answer labels printed in the supplied text. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Literal symbolic expression printed beside each answer.  The variables are
dimensionless mode number `n`, action readout `h`, mass readout `m`, and length
readout `d`; this definition records the source verbatim and is not a physical
law used by the theorem.
-/
def displayedSymbolicEnergyFormula
    (choice : AnswerChoice) (n : ℕ) (h m d : ℝ) : ℝ :=
  match choice with
  | .A => (n : ℝ) ^ 2 * h ^ 2 / (2 * Real.pi ^ 2 * m * d ^ 2)
  | .B => (n : ℝ) ^ 2 * h ^ 2 / (4 * Real.pi ^ 2 * m * d ^ 2)
  | .C => (n : ℝ) ^ 2 * h ^ 2 / (8 * Real.pi ^ 2 * m * d ^ 2)
  | .D => (n : ℝ) * h ^ 2 / (4 * Real.pi ^ 2 * m * d ^ 2)

/-- Answer label recorded by the dataset, retained independently of the model. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-! ## Derived quantum numbers, dimensions, and energy -/

/-!
The five maxima on the horizontal line determine `n_x = 5`, while the three
maxima on the vertical line determine `n_y = 3`.
-/
lemma quantumNumbers_from_probe_peak_counts
    (setup : RectangularWellElectronSetup)
    (h_readouts : MatchesDetectionProbeReadouts setup)
    (h_laws : SatisfiesInfiniteRectangularWellLaws setup) :
    setup.quantumNumber .x = 5 ∧ setup.quantumNumber .y = 3 := by
  constructor
  · simpa only [ProbeLine.variedAxis,
      h_readouts.horizontalProbeHasFiveMaxima] using
      h_laws.quantumNumberCountsProbeMaxima
        ProbeLine.horizontalBisectorOfLy
  · simpa only [ProbeLine.variedAxis,
      h_readouts.verticalProbeHasThreeMaxima] using
      h_laws.quantumNumberCountsProbeMaxima
        ProbeLine.verticalBisectorOfLx

/-!
Since adjacent maxima of `sin^2(nπx/L)` are separated by `L/n`, the scans give
`L_x = 5(3 nm) = 15 nm` and `L_y = 3(2 nm) = 6 nm`.
-/
lemma sideLengths_from_probe_peak_spacings
    (setup : RectangularWellElectronSetup)
    (h_readouts : MatchesDetectionProbeReadouts setup)
    (h_laws : SatisfiesInfiniteRectangularWellLaws setup) :
    lengthInNanometers (setup.sideLength .x) = 15 ∧
      lengthInNanometers (setup.sideLength .y) = 6 := by
  have hnano_scale (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have h := length.property
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
    have hv :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    simp only [lengthInNanometers, lengthInMeters, lengthReadout] at hv ⊢
    rw [hv]
    change
      ((UnitChoices.SI.dimScale
        ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
        L𝓭 : NNReal) : ℝ) * _ = _
    congr 1
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.toReal]
  have hx_m :
      lengthInMeters (setup.sideLength .x) =
        5 * lengthInMeters
          (setup.probeObservation .horizontalBisectorOfLy).adjacentMaximumSpacing := by
    simpa only [ProbeLine.variedAxis,
      h_readouts.horizontalProbeHasFiveMaxima, Nat.cast_ofNat] using
      h_laws.sideLengthEqualsPeakCountTimesSpacing
        ProbeLine.horizontalBisectorOfLy
  have hy_m :
      lengthInMeters (setup.sideLength .y) =
        3 * lengthInMeters
          (setup.probeObservation .verticalBisectorOfLx).adjacentMaximumSpacing := by
    simpa only [ProbeLine.variedAxis,
      h_readouts.verticalProbeHasThreeMaxima, Nat.cast_ofNat] using
      h_laws.sideLengthEqualsPeakCountTimesSpacing
        ProbeLine.verticalBisectorOfLx
  constructor
  · calc
      lengthInNanometers (setup.sideLength .x) =
          1000000000 * lengthInMeters (setup.sideLength .x) :=
        hnano_scale _
      _ = 5 *
          (1000000000 * lengthInMeters
            (setup.probeObservation
              .horizontalBisectorOfLy).adjacentMaximumSpacing) := by
        rw [hx_m]
        ring
      _ = 5 * lengthInNanometers
          (setup.probeObservation
            .horizontalBisectorOfLy).adjacentMaximumSpacing := by
        rw [hnano_scale]
      _ = 15 := by
        rw [h_readouts.horizontalProbeSpacingIsThreeNanometers]
        norm_num
  · calc
      lengthInNanometers (setup.sideLength .y) =
          1000000000 * lengthInMeters (setup.sideLength .y) :=
        hnano_scale _
      _ = 3 *
          (1000000000 * lengthInMeters
            (setup.probeObservation
              .verticalBisectorOfLx).adjacentMaximumSpacing) := by
        rw [hy_m]
        ring
      _ = 3 * lengthInNanometers
          (setup.probeObservation
            .verticalBisectorOfLx).adjacentMaximumSpacing := by
        rw [hnano_scale]
      _ = 6 := by
        rw [h_readouts.verticalProbeSpacingIsTwoNanometers]
        norm_num

/-!
Substituting the two scan spacings into the two-dimensional spectrum eliminates
the mode numbers and side lengths: `n_x/L_x = 1/(3 nm)` and
`n_y/L_y = 1/(2 nm)`.
-/
lemma energy_from_probe_spacings
    (setup : RectangularWellElectronSetup)
    (h_readouts : MatchesDetectionProbeReadouts setup)
    (h_laws : SatisfiesInfiniteRectangularWellLaws setup)
    (h_physical : HasPhysicalRectangularWellParameters setup) :
    energyInJoules setup.stateEnergy =
      actionInJouleSeconds setup.ordinaryPlanckAction ^ 2 /
        (8 * massInKilograms setup.particleMass) *
          (1 / (3e-9 : ℝ) ^ 2 + 1 / (2e-9 : ℝ) ^ 2) := by
  have hnano_scale (length : LengthQuantity) :
      lengthInNanometers length =
        1000000000 * lengthInMeters length := by
    have h := length.property
      UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
    have hv :=
      congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    simp only [lengthInNanometers, lengthInMeters, lengthReadout] at hv ⊢
    rw [hv]
    change
      ((UnitChoices.SI.dimScale
        ({UnitChoices.SI with length := LengthUnit.nanometers} : UnitChoices)
        L𝓭 : NNReal) : ℝ) * _ = _
    congr 1
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.toReal]
  have hx_spacing :
      lengthInMeters
          (setup.probeObservation
            .horizontalBisectorOfLy).adjacentMaximumSpacing =
        (3e-9 : ℝ) := by
    have hconversion :=
      hnano_scale
        (setup.probeObservation
          .horizontalBisectorOfLy).adjacentMaximumSpacing
    rw [h_readouts.horizontalProbeSpacingIsThreeNanometers] at hconversion
    norm_num at hconversion ⊢
    linarith
  have hy_spacing :
      lengthInMeters
          (setup.probeObservation
            .verticalBisectorOfLx).adjacentMaximumSpacing =
        (2e-9 : ℝ) := by
    have hconversion :=
      hnano_scale
        (setup.probeObservation
          .verticalBisectorOfLx).adjacentMaximumSpacing
    rw [h_readouts.verticalProbeSpacingIsTwoNanometers] at hconversion
    norm_num at hconversion ⊢
    linarith
  have hx_m :
      lengthInMeters (setup.sideLength .x) = 5 * (3e-9 : ℝ) := by
    simpa only [ProbeLine.variedAxis,
      h_readouts.horizontalProbeHasFiveMaxima, Nat.cast_ofNat,
      hx_spacing] using
      h_laws.sideLengthEqualsPeakCountTimesSpacing
        ProbeLine.horizontalBisectorOfLy
  have hy_m :
      lengthInMeters (setup.sideLength .y) = 3 * (2e-9 : ℝ) := by
    simpa only [ProbeLine.variedAxis,
      h_readouts.verticalProbeHasThreeMaxima, Nat.cast_ofNat,
      hy_spacing] using
      h_laws.sideLengthEqualsPeakCountTimesSpacing
        ProbeLine.verticalBisectorOfLx
  have hquantum :=
    quantumNumbers_from_probe_peak_counts setup h_readouts h_laws
  rw [h_laws.twoDimensionalEnergySpectrum, hquantum.1, hquantum.2,
    hx_m, hy_m]
  norm_num

/-!
The measured peak pattern and the two-dimensional infinite-well spectrum give

`E = (2πℏ)^2/(8m_e) * ((3 nm)⁻2 + (2 nm)⁻2)`

or approximately `2.17557e-20 J = 0.135789 eV`.

This formalizes `thm:physics:phyx_mini_0584:target`.  Neither this exact
energy, its electron-volt approximation, nor the derived quantum numbers and
side lengths appears in any premise structure.
-/
theorem problem_phyx_mini_0584
    (setup : RectangularWellElectronSetup)
    (h_scenario : MatchesRectangularWellElectronScenario setup)
    (h_figure : MatchesPrimaryRectangularWellFigure setup.figure)
    (h_readouts : MatchesDetectionProbeReadouts setup)
    (h_electron : UsesElectronReferenceData setup)
    (h_planck : UsesStandardPlanckConstant setup)
    (h_laws : SatisfiesInfiniteRectangularWellLaws setup)
    (h_physical : HasPhysicalRectangularWellParameters setup) :
    energyInJoules setup.stateEnergy =
        (2 * Real.pi * (Constants.ℏ : ℝ)) ^ 2 /
          (8 * 9.1093837139e-31) *
            (1 / (3e-9 : ℝ) ^ 2 + 1 / (2e-9 : ℝ) ^ 2) ∧
      abs (energyInElectronVolts setup.stateEnergy - 0.135789) < 1e-6 := by
  have henergy :=
    energy_from_probe_spacings setup h_readouts h_laws h_physical
  have hev :
      energyInJoules DimEnergy.electronVolt = 1.602176634e-19 := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply]
  constructor
  · rw [henergy, h_planck.ordinaryPlanckActionSI,
      h_electron.electronMassKilograms]
  · rw [energyInElectronVolts, hev, henergy,
      h_planck.ordinaryPlanckActionSI, h_electron.electronMassKilograms]
    norm_num [Constants.ℏ]
    rw [abs_lt]
    constructor <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]

end PhyXMiniProblems.ProblemPhyXMini0584
