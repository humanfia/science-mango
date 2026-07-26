import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0895

open Dimension
open scoped BigOperators

/-!
# Net electrostatic force on the `-10 nC` charge

The primary image `895.png` shows three point charges at three corners of a
rectangle.  A `+15 nC` charge is at the top-left corner, a `-5.0 nC` charge is
at the top-right corner, and the target `-10 nC` charge is at the bottom-right
corner.  The top horizontal separation is `3.0 cm` and the right vertical
separation is `1.0 cm`.

Charges, lengths, positions, forces, and the requested force magnitude are
unit-independent Physlib `Dimensionful` quantities.  Real scalars and vectors
are used only as explicit coherent-SI readouts in coulombs, metres, and
newtons, or as literal values printed in the figure and answer choices.

Assumption/target split:

* governing laws: the signed vector form of Coulomb's law for each of the two
  sources, force superposition, and agreement between the physical magnitude
  and the norm of the resultant force vector;
* previous-part results: none;
* figure/data readouts: the three charge signs and nanocoulomb labels, their
  three corner locations, the `3.0 cm` and `1.0 cm` separations, the dashed
  guide geometry, and a school-level SI calibration of Coulomb's constant;
* current target conclusions: the force magnitude rounds to
  `4.3 * 10⁻³ N`, and C is the unique closest displayed choice.

No target magnitude or answer label occurs in a setup field or theorem
premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent planar position. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent planar force vector. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coherent-SI readout of a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of a signed charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI Cartesian position vector, in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Coherent-SI Cartesian force vector, in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Coherent-SI readout of a physical force magnitude, in newtons. -/
def forceMagnitudeInNewtons (magnitude : ForceMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The three corners occupied by charges in the primary image. -/
inductive ChargeSite where
  | topLeft
  | topRight
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The three particles, named by physical role and image location. -/
inductive Particle where
  | positive15nC
  | negative5nC
  | targetNegative10nC
  deriving DecidableEq, Fintype, Repr

/-- The two particles which exert force on the target particle. -/
inductive ForceSource where
  | positive15nC
  | negative5nC
  deriving DecidableEq, Fintype, Repr

/-- Particle associated with each source-force contribution. -/
def sourceParticle : ForceSource → Particle
  | .positive15nC => .positive15nC
  | .negative5nC => .negative5nC

/-- Site occupied by each named particle in the supplied raster. -/
def expectedParticleSite : Particle → ChargeSite
  | .positive15nC => .topLeft
  | .negative5nC => .topRight
  | .targetNegative10nC => .bottomRight

/-- Signed nanocoulomb value printed beside each particle. -/
def expectedChargeInNanocoulombs : Particle → ℝ
  | .positive15nC => 15
  | .negative5nC => -5
  | .targetNegative10nC => -10

/-- Colour used for a charge circle in the supplied figure. -/
inductive FigureChargeColor where
  | red
  | teal
  deriving DecidableEq, Repr

/-- Sign glyph drawn inside a charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Expected circle colour of each particle. -/
def expectedParticleColor : Particle → FigureChargeColor
  | .positive15nC => .red
  | .negative5nC => .teal
  | .targetNegative10nC => .teal

/-- Expected sign glyph of each particle. -/
def expectedParticleSign : Particle → FigureChargeSign
  | .positive15nC => .plus
  | .negative5nC => .minus
  | .targetNegative10nC => .minus

/-- The two dashed charge-to-charge segments carrying numerical labels. -/
inductive LabelledSeparation where
  | topHorizontal
  | rightVertical
  deriving DecidableEq, Fintype, Repr

/-- Literal presentation data transcribed from image `895.png`. -/
structure ThreeChargeFigure where
  particleSite : Particle → ChargeSite
  particleColor : Particle → FigureChargeColor
  particleSign : Particle → FigureChargeSign
  printedChargeNanocoulombs : Particle → ℝ
  separationLabelCentimeters : LabelledSeparation → ℝ
  topSegmentDashed : Bool
  rightSegmentDashed : Bool
  bottomGuideDashed : Bool
  leftGuideDashed : Bool
  topSegmentHorizontal : Bool
  rightSegmentVertical : Bool
  rightAngleAtTopRight : Bool
  containsNumericalForceReadout : Bool

/-!
Independent physical quantities and force observables in the problem.

In particular, the pairwise forces, resultant force, and resultant magnitude
are not defined from an answer choice.  They are constrained only by the
governing-law predicates below.
-/
structure ThreePointChargeSetup where
  figure : ThreeChargeFigure
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  position : Particle → PlanarPositionQuantity
  charge : Particle → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  forceOnTargetFrom : ForceSource → PlanarForceQuantity
  resultantForceOnTarget : PlanarForceQuantity
  resultantForceMagnitude : ForceMagnitudeQuantity

/-- Displacement from a source particle to the target particle, in metres. -/
def displacementFromSourceToTargetInMeters
    (setup : ThreePointChargeSetup)
    (source : ForceSource) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.position .targetNegative10nC) -
    positionVectorInMeters (setup.position (sourceParticle source))

/-! ## Primary-image evidence and physical branch conditions -/

/-!
All unambiguous qualitative and numerical data transcribed from the primary
raster, together with its association to the independent physical charges,
lengths, and positions.  No force magnitude appears here.
-/
structure MatchesSuppliedThreeChargeFigure
    (setup : ThreePointChargeSetup) : Prop where
  particleLocations : ∀ particle,
    setup.figure.particleSite particle = expectedParticleSite particle
  particleColors : ∀ particle,
    setup.figure.particleColor particle = expectedParticleColor particle
  particleSignGlyphs : ∀ particle,
    setup.figure.particleSign particle = expectedParticleSign particle
  printedChargeLabels : ∀ particle,
    setup.figure.printedChargeNanocoulombs particle =
      expectedChargeInNanocoulombs particle
  physicalChargesMatchLabels : ∀ particle,
    chargeInNanocoulombs (setup.charge particle) =
      setup.figure.printedChargeNanocoulombs particle
  topSeparationLabel :
    setup.figure.separationLabelCentimeters .topHorizontal = 3
  rightSeparationLabel :
    setup.figure.separationLabelCentimeters .rightVertical = 1
  horizontalSeparationMatchesLabel :
    lengthInCentimeters setup.horizontalSeparation =
      setup.figure.separationLabelCentimeters .topHorizontal
  verticalSeparationMatchesLabel :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.separationLabelCentimeters .rightVertical
  topSegmentIsDashed : setup.figure.topSegmentDashed = true
  rightSegmentIsDashed : setup.figure.rightSegmentDashed = true
  bottomGuideIsDashed : setup.figure.bottomGuideDashed = true
  leftGuideIsDashed : setup.figure.leftGuideDashed = true
  topSegmentIsHorizontal : setup.figure.topSegmentHorizontal = true
  rightSegmentIsVertical : setup.figure.rightSegmentVertical = true
  rightAngleShownAtTopRight : setup.figure.rightAngleAtTopRight = true
  topLeftCoordinates :
    positionVectorInMeters (setup.position .positive15nC) =
      !₂[0, lengthInMeters setup.verticalSeparation]
  topRightCoordinates :
    positionVectorInMeters (setup.position .negative5nC) =
      !₂[lengthInMeters setup.horizontalSeparation,
        lengthInMeters setup.verticalSeparation]
  bottomRightCoordinates :
    positionVectorInMeters (setup.position .targetNegative10nC) =
      !₂[lengthInMeters setup.horizontalSeparation, 0]
  noForceValuePrinted :
    setup.figure.containsNumericalForceReadout = false

/-!
The rounded Coulomb constant used in the standard multiple-choice
calculation.  Physlib's `Electromagnetism.EMSystem.coulombConstant` is the
coherent-SI scalar `1 / (4 π ε₀)` appearing in the vector force law.
-/
structure UsesSchoolCoulombConstant
    (setup : ThreePointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Positivity and source-separation conditions selecting the physical case. -/
structure HasPhysicalThreeChargeParameters
    (setup : ThreePointChargeSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  everySourceSeparatedFromTarget : ∀ source,
    0 < ‖displacementFromSourceToTargetInMeters setup source‖

/-! ## Governing electrostatic laws -/

/-!
For source charge `qₛ`, target charge `qₜ`, and displacement `r` from source
to target, the force on the target is

`F = k qₜ qₛ r / ‖r‖³`.

The signed product of charges supplies attraction or repulsion.  This general
pairwise law contains no requested numerical resultant.
-/
structure SatisfiesVectorCoulombForceLaw
    (setup : ThreePointChargeSetup) : Prop where
  forceOfEachSource : ∀ source,
    forceVectorInNewtons (setup.forceOnTargetFrom source) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .targetNegative10nC) *
          chargeInCoulombs (setup.charge (sourceParticle source)) /
        ‖displacementFromSourceToTargetInMeters setup source‖ ^ 3) •
          displacementFromSourceToTargetInMeters setup source

/-- The resultant force is the vector sum of the two pairwise forces. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : ThreePointChargeSetup) : Prop where
  resultantIsSum :
    forceVectorInNewtons setup.resultantForceOnTarget =
      ∑ source : ForceSource,
        forceVectorInNewtons (setup.forceOnTargetFrom source)

/-!
The independent nonnegative magnitude observable is the Euclidean norm of the
resultant planar force vector.
-/
structure SatisfiesResultantForceMagnitudeLaw
    (setup : ThreePointChargeSetup) : Prop where
  magnitudeIsNorm :
    forceMagnitudeInNewtons setup.resultantForceMagnitude =
      ‖forceVectorInNewtons setup.resultantForceOnTarget‖

/-! ## Displayed choices and current target -/

/-- Labels attached to the four force-magnitude choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed magnitude beside each answer choice, in newtons. -/
def displayedForceMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 1.25 / 1000
  | .B => 1.35 / 1000
  | .C => 4.3 / 1000
  | .D => 1.33 / 1000

/-!
`value` rounds to `displayed` at a stated display resolution when it lies
strictly within half a resolution step.  For `4.3 * 10⁻³ N`, the last printed
digit has resolution `0.1 * 10⁻³ N`.
-/
def RoundsToAtResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |value - displayed| < resolution / 2

/-! A choice is uniquely closest to the independently modelled magnitude. -/
def IsUniqueClosestDisplayedForceChoice
    (setup : ThreePointChargeSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |forceMagnitudeInNewtons setup.resultantForceMagnitude -
        displayedForceMagnitudeInNewtons choice| <
      |forceMagnitudeInNewtons setup.resultantForceMagnitude -
        displayedForceMagnitudeInNewtons other|

/-!
The vector Coulomb forces from the `+15 nC` and `-5.0 nC` sources combine to
a magnitude which rounds to `4.3 * 10⁻³ N`; this is uniquely displayed as
choice C.

This declaration formalizes
`thm:physics:phyx_mini_0895:target`.
-/
theorem problem_phyx_mini_0895
    (setup : ThreePointChargeSetup)
    (h_figure : MatchesSuppliedThreeChargeFigure setup)
    (h_constant : UsesSchoolCoulombConstant setup)
    (h_physical : HasPhysicalThreeChargeParameters setup)
    (h_coulomb : SatisfiesVectorCoulombForceLaw setup)
    (h_superposition : SatisfiesElectrostaticForceSuperposition setup)
    (h_magnitude : SatisfiesResultantForceMagnitudeLaw setup) :
    RoundsToAtResolution
        (forceMagnitudeInNewtons setup.resultantForceMagnitude)
        (displayedForceMagnitudeInNewtons .C)
        (0.1 / 1000) ∧
      IsUniqueClosestDisplayedForceChoice setup .C := by
  have hHorizontal :
      lengthInMeters setup.horizontalSeparation = (3 : ℝ) / 100 := by
    have h := h_figure.horizontalSeparationMatchesLabel
    rw [h_figure.topSeparationLabel] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hVertical :
      lengthInMeters setup.verticalSeparation = (1 : ℝ) / 100 := by
    have h := h_figure.verticalSeparationMatchesLabel
    rw [h_figure.rightSeparationLabel] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hTargetCharge :
      chargeInCoulombs (setup.charge .targetNegative10nC) =
        -(10 / (10 : ℝ) ^ 9) := by
    have h := h_figure.physicalChargesMatchLabels .targetNegative10nC
    rw [h_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hNegativeCharge :
      chargeInCoulombs (setup.charge .negative5nC) =
        -(5 / (10 : ℝ) ^ 9) := by
    have h := h_figure.physicalChargesMatchLabels .negative5nC
    rw [h_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hPositiveCharge :
      chargeInCoulombs (setup.charge .positive15nC) =
        15 / (10 : ℝ) ^ 9 := by
    have h := h_figure.physicalChargesMatchLabels .positive15nC
    rw [h_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hNegativeDisplacement :
      displacementFromSourceToTargetInMeters setup .negative5nC =
        !₂[(0 : ℝ), -(1 : ℝ) / 100] := by
    rw [displacementFromSourceToTargetInMeters, sourceParticle,
      h_figure.bottomRightCoordinates, h_figure.topRightCoordinates,
      hHorizontal, hVertical]
    ext i
    fin_cases i <;> norm_num
  have hPositiveDisplacement :
      displacementFromSourceToTargetInMeters setup .positive15nC =
        !₂[(3 : ℝ) / 100, -(1 : ℝ) / 100] := by
    rw [displacementFromSourceToTargetInMeters, sourceParticle,
      h_figure.bottomRightCoordinates, h_figure.topLeftCoordinates,
      hHorizontal, hVertical]
    ext i
    fin_cases i <;> norm_num
  have hSqrtTenSquared : (Real.sqrt 10) ^ 2 = (10 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtTenPositive : 0 < Real.sqrt 10 :=
    Real.sqrt_pos.2 (by norm_num)
  have hNegativeDisplacementNorm :
      ‖displacementFromSourceToTargetInMeters setup .negative5nC‖ =
        (1 : ℝ) / 100 := by
    rw [hNegativeDisplacement]
    have hSq :
        ‖(!₂[(0 : ℝ), -(1 : ℝ) / 100] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
          (1 : ℝ) / 10000 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [Fin.sum_univ_two]
    nlinarith only [hSq,
      norm_nonneg
        (!₂[(0 : ℝ), -(1 : ℝ) / 100] :
          EuclideanSpace ℝ (Fin 2))]
  have hPositiveDisplacementNorm :
      ‖displacementFromSourceToTargetInMeters setup .positive15nC‖ =
        Real.sqrt 10 / 100 := by
    rw [hPositiveDisplacement]
    have hSq :
        ‖(!₂[(3 : ℝ) / 100, -(1 : ℝ) / 100] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
          (1 : ℝ) / 1000 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [Fin.sum_univ_two]
    nlinarith only [hSq, hSqrtTenSquared, hSqrtTenPositive,
      norm_nonneg
        (!₂[(3 : ℝ) / 100, -(1 : ℝ) / 100] :
          EuclideanSpace ℝ (Fin 2))]
  have hNegativeForce :
      forceVectorInNewtons (setup.forceOnTargetFrom .negative5nC) =
        !₂[(0 : ℝ), -(9 : ℝ) / 2000] := by
    rw [h_coulomb.forceOfEachSource, sourceParticle,
      h_constant.coulombConstantCalibration, hTargetCharge, hNegativeCharge,
      hNegativeDisplacementNorm, hNegativeDisplacement]
    ext i
    fin_cases i <;> norm_num
  have hPositiveForce :
      forceVectorInNewtons (setup.forceOnTargetFrom .positive15nC) =
        !₂[-(81 * Real.sqrt 10) / 200000,
          27 * Real.sqrt 10 / 200000] := by
    rw [h_coulomb.forceOfEachSource, sourceParticle,
      h_constant.coulombConstantCalibration, hTargetCharge, hPositiveCharge,
      hPositiveDisplacementNorm, hPositiveDisplacement]
    ext i
    fin_cases i
    · simp
      field_simp
      nlinarith only [hSqrtTenSquared]
    · simp
      field_simp
      nlinarith only [hSqrtTenSquared]
  have hSourceSum
      (f : ForceSource → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : ForceSource, f source =
        f .positive15nC + f .negative5nC := by
    rw [show (Finset.univ : Finset ForceSource) =
      {.positive15nC, .negative5nC} by decide]
    simp
  have hResultant :
      forceVectorInNewtons setup.resultantForceOnTarget =
        !₂[-(81 * Real.sqrt 10) / 200000,
          (27 * Real.sqrt 10 - 900) / 200000] := by
    rw [h_superposition.resultantIsSum, hSourceSum,
      hPositiveForce, hNegativeForce]
    ext i
    fin_cases i <;> simp <;> ring
  have hMagnitudeSquared :
      (forceMagnitudeInNewtons setup.resultantForceMagnitude) ^ 2 =
        (8829 - 486 * Real.sqrt 10) / 400000000 := by
    rw [h_magnitude.magnitudeIsNorm, hResultant]
    have hSq := EuclideanSpace.real_norm_sq_eq
      (!₂[-(81 * Real.sqrt 10) / 200000,
        (27 * Real.sqrt 10 - 900) / 200000] :
          EuclideanSpace ℝ (Fin 2))
    norm_num [Fin.sum_univ_two] at hSq
    nlinarith only [hSq, hSqrtTenSquared]
  have hSqrtTenLower : (316 : ℝ) / 100 < Real.sqrt 10 := by
    nlinarith only [hSqrtTenSquared, hSqrtTenPositive]
  have hSqrtTenUpper : Real.sqrt 10 < (317 : ℝ) / 100 := by
    nlinarith only [hSqrtTenSquared, hSqrtTenPositive]
  have hMagnitudeNonnegative :
      0 ≤ forceMagnitudeInNewtons setup.resultantForceMagnitude := by
    rw [h_magnitude.magnitudeIsNorm]
    exact norm_nonneg _
  have hMagnitudeLower :
      (425 : ℝ) / 100000 <
        forceMagnitudeInNewtons setup.resultantForceMagnitude := by
    nlinarith only [hMagnitudeSquared, hSqrtTenUpper,
      hMagnitudeNonnegative]
  have hMagnitudeUpper :
      forceMagnitudeInNewtons setup.resultantForceMagnitude <
        (435 : ℝ) / 100000 := by
    nlinarith only [hMagnitudeSquared, hSqrtTenLower,
      hMagnitudeNonnegative]
  have hRoundingError :
      |forceMagnitudeInNewtons setup.resultantForceMagnitude -
          displayedForceMagnitudeInNewtons .C| <
        (0.1 / 1000) / 2 := by
    rw [abs_lt]
    constructor <;>
      norm_num [displayedForceMagnitudeInNewtons] at ⊢ <;>
      linarith only [hMagnitudeLower, hMagnitudeUpper]
  constructor
  · exact ⟨by norm_num, hRoundingError⟩
  · unfold IsUniqueClosestDisplayedForceChoice
    intro other hOther
    fin_cases other
    · calc
        |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .C| <
            (0.1 / 1000) / 2 := hRoundingError
        _ < |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .A| := by
          rw [abs_of_pos]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]
    · calc
        |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .C| <
            (0.1 / 1000) / 2 := hRoundingError
        _ < |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .B| := by
          rw [abs_of_pos]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]
    · exact (hOther rfl).elim
    · calc
        |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .C| <
            (0.1 / 1000) / 2 := hRoundingError
        _ < |forceMagnitudeInNewtons setup.resultantForceMagnitude -
            displayedForceMagnitudeInNewtons .D| := by
          rw [abs_of_pos]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]
          · norm_num [displayedForceMagnitudeInNewtons] at ⊢
            linarith only [hMagnitudeLower]

end PhyXMiniProblems.ProblemPhyXMini0895
