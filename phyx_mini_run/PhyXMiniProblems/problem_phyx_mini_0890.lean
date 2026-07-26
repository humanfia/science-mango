import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0890

open Dimension

/-!
# Net electric force on one corner charge of a rectangle

The primary image `890.png` places `q₃ = +30 nC` at the top-left corner of a
`5.0 cm` by `10.0 cm` rectangle, `q₁ = -50 nC` at the bottom-left corner, and
`q₂ = +50 nC` at the bottom-right corner.  Thus the force of `q₁` on `q₃` is
downward, while the force of `q₂` on `q₃` is directed up and left along the
rectangle's diagonal.  Their vector sum points down and left.

Charges, lengths, positions, and force vectors are unit-independent Physlib
quantities.  Real numbers occur only at explicit coherent-SI readout
boundaries, as printed figure values, or as displayed answer values.

Assumption/target split:

* governing laws: signed vector Coulomb force between distinct point charges
  and superposition of the pair forces;
* previous-part results: none;
* figure/data readouts: the three signed nanocoulomb labels, the `5.0 cm`
  width, the `10.0 cm` height, the occupied rectangle corners, the dashed
  sides, and the rounded school value `k = 9 * 10^9` in SI units;
* current target conclusions: the net force on `q₃` points down and left, and
  its magnitude agrees to displayed precision with choice C,
  `6.2 * 10^-4 N`.

No premise or setup field states the requested force direction, magnitude, or
answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent physical position in the plane of the figure. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent physical force vector in the plane of the figure. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coherent-SI readout of a signed charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three charge labels in the image. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI Cartesian position readout, whose coordinates are in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Coherent-SI planar-force readout, whose coordinates are in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Euclidean magnitude in newtons of a dimensionful planar force. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-! ## Named particles and primary-figure vocabulary -/

/-- The three charged particles named in the source and the image. -/
inductive Particle where
  | q1
  | q2
  | q3
  deriving DecidableEq, Fintype, Repr

/-- The four corners of the dashed rectangle. -/
inductive RectangleCorner where
  | topLeft
  | topRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The four dashed sides visible in the primary image. -/
inductive RectangleSide where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The plus or minus glyph drawn inside each charge circle. -/
inductive FigureChargeGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The physical idealization used when applying the point-charge law. -/
inductive ChargedParticleModel where
  | pointParticle
  | spatiallyExtended
  deriving DecidableEq, Repr

/-- Corner occupied by each named particle in image `890.png`. -/
def expectedCorner : Particle → RectangleCorner
  | .q1 => .bottomLeft
  | .q2 => .bottomRight
  | .q3 => .topLeft

/-- Charge-sign glyph visibly attached to each particle. -/
def expectedChargeGlyph : Particle → FigureChargeGlyph
  | .q1 => .minus
  | .q2 => .plus
  | .q3 => .plus

/-!
Literal presentation content transcribed from the primary raster.  The image
does not display a net-force vector, magnitude, or answer choice.
-/
structure ThreeChargeRectangleFigure where
  particleShown : Particle → Bool
  particleCorner : Particle → RectangleCorner
  chargeGlyph : Particle → FigureChargeGlyph
  printedChargeNanocoulombs : Particle → ℝ
  dashedSideShown : RectangleSide → Bool
  widthLabelCentimeters : ℝ
  heightLabelCentimeters : ℝ
  containsNetForceVector : Bool
  containsNetForceMagnitude : Bool

/-!
Independent physical objects in the electrostatic setup.  In particular,
`netForceOn` and `pairForceOnDueTo` are observables constrained by the laws
below; neither is defined from a displayed answer.
-/
structure ThreeChargeRectangleSetup where
  charge : Particle → SignedChargeQuantity
  position : Particle → PlanarPositionQuantity
  rectangleWidth : LengthQuantity
  rectangleHeight : LengthQuantity
  particleModel : Particle → ChargedParticleModel
  pairForceOnDueTo : Particle → Particle → PlanarForceQuantity
  netForceOn : Particle → PlanarForceQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : ThreeChargeRectangleFigure

/-! ## Geometry, source data, and governing electrostatics -/

/-- Displacement from a source particle to a target particle, in metres. -/
def displacementVectorInMeters
    (setup : ThreeChargeRectangleSetup)
    (target source : Particle) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters (setup.position target) -
    positionVectorInMeters (setup.position source)

/-- Euclidean separation of two particles, in metres. -/
def separationInMeters
    (setup : ThreeChargeRectangleSetup)
    (target source : Particle) : ℝ :=
  ‖displacementVectorInMeters setup target source‖

/-!
The numerical physical data stated in the problem.  These are charge and
length readouts only and contain no force value.
-/
structure HasThreeChargeRectangleProblemData
    (setup : ThreeChargeRectangleSetup) : Prop where
  q1ChargeNanocoulombs : chargeInNanocoulombs (setup.charge .q1) = -50
  q2ChargeNanocoulombs : chargeInNanocoulombs (setup.charge .q2) = 50
  q3ChargeNanocoulombs : chargeInNanocoulombs (setup.charge .q3) = 30
  rectangleWidthCentimeters :
    lengthInCentimeters setup.rectangleWidth = 5
  rectangleHeightCentimeters :
    lengthInCentimeters setup.rectangleHeight = 10

/-!
Unambiguous evidence read from `890.png`.  In contrast with the auxiliary
caption, the primary raster places `q₂` at the bottom-right corner, so the
line from `q₂` to `q₃` is the rectangle diagonal.
-/
structure MatchesPrimaryThreeChargeFigure
    (setup : ThreeChargeRectangleSetup) : Prop where
  everyParticleShown : ∀ particle,
    setup.figure.particleShown particle = true
  cornersMatchImage : ∀ particle,
    setup.figure.particleCorner particle = expectedCorner particle
  glyphsMatchImage : ∀ particle,
    setup.figure.chargeGlyph particle = expectedChargeGlyph particle
  printedQ1Charge : setup.figure.printedChargeNanocoulombs .q1 = -50
  printedQ2Charge : setup.figure.printedChargeNanocoulombs .q2 = 50
  printedQ3Charge : setup.figure.printedChargeNanocoulombs .q3 = 30
  physicalChargesMatchPrintedLabels : ∀ particle,
    chargeInNanocoulombs (setup.charge particle) =
      setup.figure.printedChargeNanocoulombs particle
  everyRectangleSideDashed : ∀ side,
    setup.figure.dashedSideShown side = true
  printedWidth : setup.figure.widthLabelCentimeters = 5
  printedHeight : setup.figure.heightLabelCentimeters = 10
  widthLabelMatchesPhysicalLength :
    setup.figure.widthLabelCentimeters =
      lengthInCentimeters setup.rectangleWidth
  heightLabelMatchesPhysicalLength :
    setup.figure.heightLabelCentimeters =
      lengthInCentimeters setup.rectangleHeight
  noNetForceVectorInImage : setup.figure.containsNetForceVector = false
  noNetForceMagnitudeInImage : setup.figure.containsNetForceMagnitude = false

/-!
The coordinate consequences of the occupied rectangle corners.  Translation
of the whole diagram remains free: only the relative horizontal and vertical
coordinates are fixed.
-/
structure SatisfiesDisplayedRectangleGeometry
    (setup : ThreeChargeRectangleSetup) : Prop where
  q1AndQ3ShareLeftCoordinate :
    positionVectorInMeters (setup.position .q1) xAxis =
      positionVectorInMeters (setup.position .q3) xAxis
  q1AndQ2ShareBottomCoordinate :
    positionVectorInMeters (setup.position .q1) yAxis =
      positionVectorInMeters (setup.position .q2) yAxis
  q2IsOneWidthRightOfQ1 :
    positionVectorInMeters (setup.position .q2) xAxis -
        positionVectorInMeters (setup.position .q1) xAxis =
      lengthInMeters setup.rectangleWidth
  q3IsOneHeightAboveQ1 :
    positionVectorInMeters (setup.position .q3) yAxis -
        positionVectorInMeters (setup.position .q1) yAxis =
      lengthInMeters setup.rectangleHeight

/-- Point-particle and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalThreeChargeParameters
    (setup : ThreeChargeRectangleSetup) : Prop where
  everyChargeIsPointlike : ∀ particle,
    setup.particleModel particle = .pointParticle
  widthPositive : 0 < lengthInMeters setup.rectangleWidth
  heightPositive : 0 < lengthInMeters setup.rectangleHeight
  distinctParticlesSeparated : ∀ target source,
    target ≠ source → 0 < separationInMeters setup target source
  everyChargeNonzero : ∀ particle,
    chargeInCoulombs (setup.charge particle) ≠ 0
  vacuumPermittivityPositive : 0 < setup.electromagneticSystem.ε₀
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The rounded Coulomb constant customarily used for the multiple-choice
calculation, expressed in coherent SI units `N m² / C²`.
-/
structure UsesRoundedSchoolCoulombConstant
    (setup : ThreeChargeRectangleSetup) : Prop where
  coulombConstantSI :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-!
For distinct point charges, the signed vector Coulomb law is

`F(target <- source) = k q_target q_source (r_target - r_source) / |r|^3`.

The second field states vector superposition over every other named particle.
These are general governing laws and contain no requested numerical force or
answer choice.
-/
structure SatisfiesPointChargeCoulombAndSuperpositionLaws
    (setup : ThreeChargeRectangleSetup) : Prop where
  pairwiseCoulombForce : ∀ target source,
    target ≠ source →
      separationInMeters setup target source ≠ 0 →
        forceVectorInNewtons (setup.pairForceOnDueTo target source) =
          (setup.electromagneticSystem.coulombConstant *
              chargeInCoulombs (setup.charge target) *
              chargeInCoulombs (setup.charge source) /
              separationInMeters setup target source ^ 3) •
            displacementVectorInMeters setup target source
  forceSuperposition : ∀ target,
    forceVectorInNewtons (setup.netForceOn target) =
      ∑ source : Particle,
        if source = target then 0
        else forceVectorInNewtons (setup.pairForceOnDueTo target source)

/-! ## Derived geometry and force relations -/

/-!
The two source-to-target separations are respectively the rectangle height
and its diagonal.  This follows from the primary-image corner layout and is
not an independent figure readout.
-/
lemma q3_pair_separations
    (setup : ThreeChargeRectangleSetup)
    (_geometry : SatisfiesDisplayedRectangleGeometry setup)
    (_physical : HasPhysicalThreeChargeParameters setup) :
    separationInMeters setup .q3 .q1 =
        lengthInMeters setup.rectangleHeight ∧
      separationInMeters setup .q3 .q2 =
        Real.sqrt
          (lengthInMeters setup.rectangleWidth ^ 2 +
            lengthInMeters setup.rectangleHeight ^ 2) := by
  rcases _geometry with ⟨hx13, hy12, hx21, hy31⟩
  simp only [xAxis, yAxis] at hx13 hy12 hx21 hy31
  have hx31' :
      positionVectorInMeters (setup.position .q3) (0 : Fin 2) -
          positionVectorInMeters (setup.position .q1) (0 : Fin 2) = 0 := by
    linarith
  have hx32' :
      positionVectorInMeters (setup.position .q3) (0 : Fin 2) -
          positionVectorInMeters (setup.position .q2) (0 : Fin 2) =
        -lengthInMeters setup.rectangleWidth := by
    linarith
  have hy31' :
      positionVectorInMeters (setup.position .q3) (1 : Fin 2) -
          positionVectorInMeters (setup.position .q1) (1 : Fin 2) =
        lengthInMeters setup.rectangleHeight := by
    linarith
  have hy32' :
      positionVectorInMeters (setup.position .q3) (1 : Fin 2) -
          positionVectorInMeters (setup.position .q2) (1 : Fin 2) =
        lengthInMeters setup.rectangleHeight := by
    linarith
  constructor
  · rw [separationInMeters, displacementVectorInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    rw [hx31', hy31', abs_zero, zero_pow, zero_add,
      abs_of_pos _physical.heightPositive,
      Real.sqrt_sq_eq_abs,
      abs_of_pos _physical.heightPositive]
    norm_num
  · rw [separationInMeters, displacementVectorInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    congr 1
    rw [hx32', hy32']
    rw [abs_neg, abs_of_pos _physical.widthPositive,
      abs_of_pos _physical.heightPositive]

/-!
Resolving the two Coulomb forces along the displayed axes gives these exact
component formulas.  The negative `q₁` term is automatically attractive
because its signed charge readout occurs in the formula.
-/
lemma netForceOnQ3_component_formulas
    (setup : ThreeChargeRectangleSetup)
    (_geometry : SatisfiesDisplayedRectangleGeometry setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_laws : SatisfiesPointChargeCoulombAndSuperpositionLaws setup) :
    forceVectorInNewtons (setup.netForceOn .q3) xAxis =
        -(setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q2) *
            lengthInMeters setup.rectangleWidth /
            (Real.sqrt
                (lengthInMeters setup.rectangleWidth ^ 2 +
                  lengthInMeters setup.rectangleHeight ^ 2)) ^ 3) ∧
      forceVectorInNewtons (setup.netForceOn .q3) yAxis =
        setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q1) /
            lengthInMeters setup.rectangleHeight ^ 2 +
          setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q2) *
            lengthInMeters setup.rectangleHeight /
            (Real.sqrt
                (lengthInMeters setup.rectangleWidth ^ 2 +
                  lengthInMeters setup.rectangleHeight ^ 2)) ^ 3 := by
  rcases q3_pair_separations setup _geometry _physical with ⟨hsep31, hsep32⟩
  rcases _geometry with ⟨hx13, hy12, hx21, hy31⟩
  simp only [xAxis, yAxis] at hx13 hy12 hx21 hy31
  have hx31 :
      positionVectorInMeters (setup.position .q3) (0 : Fin 2) -
          positionVectorInMeters (setup.position .q1) (0 : Fin 2) = 0 := by
    linarith
  have hx32 :
      positionVectorInMeters (setup.position .q3) (0 : Fin 2) -
          positionVectorInMeters (setup.position .q2) (0 : Fin 2) =
        -lengthInMeters setup.rectangleWidth := by
    linarith
  have hy31 :
      positionVectorInMeters (setup.position .q3) (1 : Fin 2) -
          positionVectorInMeters (setup.position .q1) (1 : Fin 2) =
        lengthInMeters setup.rectangleHeight := by
    linarith
  have hy32 :
      positionVectorInMeters (setup.position .q3) (1 : Fin 2) -
          positionVectorInMeters (setup.position .q2) (1 : Fin 2) =
        lengthInMeters setup.rectangleHeight := by
    linarith
  have hheight :
      lengthInMeters setup.rectangleHeight ≠ 0 :=
    ne_of_gt _physical.heightPositive
  have hdiagonal :
      Real.sqrt
          (lengthInMeters setup.rectangleWidth ^ 2 +
            lengthInMeters setup.rectangleHeight ^ 2) ≠ 0 := by
    rw [← hsep32]
    exact ne_of_gt
      (_physical.distinctParticlesSeparated .q3 .q2 (by decide))
  have hforce31 := _laws.pairwiseCoulombForce .q3 .q1 (by decide)
    (by simpa only [hsep31] using hheight)
  have hforce32 := _laws.pairwiseCoulombForce .q3 .q2 (by decide)
    (by simpa only [hsep32] using hdiagonal)
  have hsuper := _laws.forceSuperposition .q3
  rw [show (Finset.univ : Finset Particle) =
      {.q1, .q2, .q3} by
        ext particle
        fin_cases particle <;> simp] at hsuper
  simp at hsuper
  have hnetx := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (0 : Fin 2)) hsuper
  have hnety := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (1 : Fin 2)) hsuper
  have h31x := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (0 : Fin 2)) hforce31
  have h31y := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (1 : Fin 2)) hforce31
  have h32x := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (0 : Fin 2)) hforce32
  have h32y := congrArg
    (fun v : EuclideanSpace ℝ (Fin 2) => v (1 : Fin 2)) hforce32
  simp only [PiLp.add_apply] at hnetx hnety
  simp only [PiLp.smul_apply, smul_eq_mul, displacementVectorInMeters,
    PiLp.sub_apply] at h31x h31y h32x h32y
  rw [hsep31, hx31] at h31x
  rw [hsep31, hy31] at h31y
  rw [hsep32, hx32] at h32x
  rw [hsep32, hy32] at h32y
  have h31x' :
      forceVectorInNewtons (setup.pairForceOnDueTo .q3 .q1) (0 : Fin 2) =
        0 := by
    rw [h31x]
    ring
  have h31y' :
      forceVectorInNewtons (setup.pairForceOnDueTo .q3 .q1) (1 : Fin 2) =
        setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q1) /
            lengthInMeters setup.rectangleHeight ^ 2 := by
    rw [h31y]
    field_simp [hheight]
  have h32x' :
      forceVectorInNewtons (setup.pairForceOnDueTo .q3 .q2) (0 : Fin 2) =
        -(setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q2) *
            lengthInMeters setup.rectangleWidth /
            (Real.sqrt
                (lengthInMeters setup.rectangleWidth ^ 2 +
                  lengthInMeters setup.rectangleHeight ^ 2)) ^ 3) := by
    rw [h32x]
    ring
  have h32y' :
      forceVectorInNewtons (setup.pairForceOnDueTo .q3 .q2) (1 : Fin 2) =
        setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q3) *
            chargeInCoulombs (setup.charge .q2) *
            lengthInMeters setup.rectangleHeight /
            (Real.sqrt
                (lengthInMeters setup.rectangleWidth ^ 2 +
                  lengthInMeters setup.rectangleHeight ^ 2)) ^ 3 := by
    rw [h32y]
    ring
  constructor
  · simp only [xAxis]
    rw [hnetx, h31x', h32x']
    ring
  · simp only [yAxis]
    rw [hnety, h31y', h32y']

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed force-magnitude choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal force magnitude in newtons printed beside each answer label. -/
def answerChoiceForceInNewtons : AnswerChoice → ℝ
  | .A => (1.25 : ℝ) * 10 ^ (-3 : ℤ)
  | .B => (1.35 : ℝ) * 10 ^ (-3 : ℤ)
  | .C => (6.2 : ℝ) * 10 ^ (-4 : ℤ)
  | .D => (1.33 : ℝ) * 10 ^ (-3 : ℤ)

/-- Half of the last decimal place displayed in choice C. -/
def choiceCDisplayToleranceInNewtons : ℝ :=
  (0.05 : ℝ) * 10 ^ (-4 : ℤ)

/-!
A choice is closest when its printed magnitude is no farther from the
independently modeled net-force magnitude than every alternative.
-/
def IsClosestDisplayedForceMagnitude
    (force : PlanarForceQuantity) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |forceMagnitudeInNewtons force - answerChoiceForceInNewtons choice| ≤
      |forceMagnitudeInNewtons force -
        answerChoiceForceInNewtons alternative|

/-!
The signed Coulomb forces sum to a vector with negative horizontal and
vertical components.  Its magnitude is approximately `6.17 * 10^-4 N`, which
rounds to the displayed `6.2 * 10^-4 N` and uniquely selects choice C.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0890:target`.
-/
theorem problem_phyx_mini_0890
    (setup : ThreeChargeRectangleSetup)
    (_data : HasThreeChargeRectangleProblemData setup)
    (_figure : MatchesPrimaryThreeChargeFigure setup)
    (_geometry : SatisfiesDisplayedRectangleGeometry setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_constant : UsesRoundedSchoolCoulombConstant setup)
    (_laws : SatisfiesPointChargeCoulombAndSuperpositionLaws setup) :
    forceVectorInNewtons (setup.netForceOn .q3) xAxis < 0 ∧
      forceVectorInNewtons (setup.netForceOn .q3) yAxis < 0 ∧
      |forceMagnitudeInNewtons (setup.netForceOn .q3) -
          answerChoiceForceInNewtons .C| <
        choiceCDisplayToleranceInNewtons ∧
      IsClosestDisplayedForceMagnitude (setup.netForceOn .q3) .C := by
  have hq1 :
      chargeInCoulombs (setup.charge .q1) = -(1 : ℝ) / 20000000 := by
    have h := _data.q1ChargeNanocoulombs
    simp only [chargeInNanocoulombs] at h
    norm_num at h ⊢
    linarith
  have hq2 :
      chargeInCoulombs (setup.charge .q2) = (1 : ℝ) / 20000000 := by
    have h := _data.q2ChargeNanocoulombs
    simp only [chargeInNanocoulombs] at h
    norm_num at h ⊢
    linarith
  have hq3 :
      chargeInCoulombs (setup.charge .q3) = (3 : ℝ) / 100000000 := by
    have h := _data.q3ChargeNanocoulombs
    simp only [chargeInNanocoulombs] at h
    norm_num at h ⊢
    linarith
  have hwidth :
      lengthInMeters setup.rectangleWidth = (1 : ℝ) / 20 := by
    have h := _data.rectangleWidthCentimeters
    simp only [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have hheight :
      lengthInMeters setup.rectangleHeight = (1 : ℝ) / 10 := by
    have h := _data.rectangleHeightCentimeters
    simp only [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have hk :
      setup.electromagneticSystem.coulombConstant = 9000000000 := by
    have h := _constant.coulombConstantSI
    norm_num at h ⊢
    exact h
  have hsquare :
      Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hspos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 5 ≠ 0 := ne_of_gt hspos
  have hdiagonal :
      Real.sqrt (((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 10) ^ 2) =
        Real.sqrt 5 / 20 := by
    have hleftsq :
        Real.sqrt (((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 10) ^ 2) ^ 2 =
          ((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 10) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hleftnonneg :
        0 ≤ Real.sqrt (((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 10) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith only [hleftsq, hleftnonneg, hsquare, hsnonneg]
  rcases netForceOnQ3_component_formulas setup _geometry _physical _laws with
    ⟨hcomponentX, hcomponentY⟩
  have hforceX :
      forceVectorInNewtons (setup.netForceOn .q3) xAxis =
        -((27 : ℝ) / 125000 * Real.sqrt 5) := by
    rw [hcomponentX, hk, hq3, hq2, hwidth, hheight, hdiagonal]
    field_simp [hsne]
    nlinarith
  have hforceY :
      forceVectorInNewtons (setup.netForceOn .q3) yAxis =
        -(27 : ℝ) / 20000 + (54 : ℝ) / 125000 * Real.sqrt 5 := by
    rw [hcomponentY, hk, hq3, hq1, hq2, hwidth, hheight, hdiagonal]
    field_simp [hsne]
    nlinarith
  have hsqrtLower : (559 : ℝ) / 250 < Real.sqrt 5 := by
    nlinarith only [hsquare, hsnonneg]
  have hsqrtUpper : Real.sqrt 5 < (2237 : ℝ) / 1000 := by
    nlinarith only [hsquare, hsnonneg]
  simp only [xAxis, yAxis] at hforceX hforceY ⊢
  have hforceMagnitude :
      forceMagnitudeInNewtons (setup.netForceOn .q3) =
        Real.sqrt
          ((-((27 : ℝ) / 125000 * Real.sqrt 5)) ^ 2 +
            (-(27 : ℝ) / 20000 +
              (54 : ℝ) / 125000 * Real.sqrt 5) ^ 2) := by
    rw [forceMagnitudeInNewtons, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hforceX, hforceY]
  have hradicand :
      0 ≤ (-((27 : ℝ) / 125000 * Real.sqrt 5)) ^ 2 +
        (-(27 : ℝ) / 20000 +
          (54 : ℝ) / 125000 * Real.sqrt 5) ^ 2 := by
    positivity
  have hforceMagnitudeSq :
      forceMagnitudeInNewtons (setup.netForceOn .q3) ^ 2 =
        (-((27 : ℝ) / 125000 * Real.sqrt 5)) ^ 2 +
          (-(27 : ℝ) / 20000 +
            (54 : ℝ) / 125000 * Real.sqrt 5) ^ 2 := by
    rw [hforceMagnitude, Real.sq_sqrt hradicand]
  have hforceMagnitudeNonneg :
      0 ≤ forceMagnitudeInNewtons (setup.netForceOn .q3) := by
    exact norm_nonneg _
  have hforceMagnitudeLower :
      (123 : ℝ) / 200000 <
        forceMagnitudeInNewtons (setup.netForceOn .q3) := by
    nlinarith only [hforceMagnitudeSq, hforceMagnitudeNonneg,
      hsquare, hsqrtUpper]
  have hforceMagnitudeUpper :
      forceMagnitudeInNewtons (setup.netForceOn .q3) < (1 : ℝ) / 1600 := by
    nlinarith only [hforceMagnitudeSq, hforceMagnitudeNonneg,
      hsquare, hsqrtLower]
  have hxnegative :
      forceVectorInNewtons (setup.netForceOn .q3) (0 : Fin 2) < 0 := by
    rw [hforceX]
    exact neg_lt_zero.mpr (mul_pos (by norm_num) hspos)
  have hynegative :
      forceVectorInNewtons (setup.netForceOn .q3) (1 : Fin 2) < 0 := by
    rw [hforceY]
    linarith only [hsqrtUpper]
  have htolerance :
      |forceMagnitudeInNewtons (setup.netForceOn .q3) -
          answerChoiceForceInNewtons .C| <
        choiceCDisplayToleranceInNewtons := by
    norm_num [answerChoiceForceInNewtons,
      choiceCDisplayToleranceInNewtons, abs_lt]
    constructor <;>
      linarith only [hforceMagnitudeLower, hforceMagnitudeUpper]
  refine ⟨hxnegative, hynegative, htolerance, ?_⟩
  intro alternative
  cases alternative
  · have hsign :
        forceMagnitudeInNewtons (setup.netForceOn .q3) -
            answerChoiceForceInNewtons .A ≤ 0 := by
      norm_num [answerChoiceForceInNewtons]
      linarith only [hforceMagnitudeUpper]
    rw [abs_of_nonpos hsign]
    norm_num [answerChoiceForceInNewtons,
      choiceCDisplayToleranceInNewtons] at htolerance ⊢
    linarith only [htolerance, hforceMagnitudeUpper]
  · have hsign :
        forceMagnitudeInNewtons (setup.netForceOn .q3) -
            answerChoiceForceInNewtons .B ≤ 0 := by
      norm_num [answerChoiceForceInNewtons]
      linarith only [hforceMagnitudeUpper]
    rw [abs_of_nonpos hsign]
    norm_num [answerChoiceForceInNewtons,
      choiceCDisplayToleranceInNewtons] at htolerance ⊢
    linarith only [htolerance, hforceMagnitudeUpper]
  · exact le_rfl
  · have hsign :
        forceMagnitudeInNewtons (setup.netForceOn .q3) -
            answerChoiceForceInNewtons .D ≤ 0 := by
      norm_num [answerChoiceForceInNewtons]
      linarith only [hforceMagnitudeUpper]
    rw [abs_of_nonpos hsign]
    norm_num [answerChoiceForceInNewtons,
      choiceCDisplayToleranceInNewtons] at htolerance ⊢
    linarith only [htolerance, hforceMagnitudeUpper]

end PhyXMiniProblems.ProblemPhyXMini0890
