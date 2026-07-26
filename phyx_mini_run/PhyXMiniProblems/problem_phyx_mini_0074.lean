import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.Dimension

/-!
# PhyX mini problem 0074: refractive index of an equilateral prism

The primary image shows an equilateral triangular prism with apex angle `α`,
an internal ray parallel to the base, dashed interface normals, and equal
external entry and emergence angles labelled `β`.  The measured value is
`β = 52.2°`.  The internal incidence/refraction angles are consequently
`30°`, and Snell's law at either air--prism interface determines the prism's
dimensionless refractive index.

Angles are represented by Mathlib's `Real.Angle`; refractive indices and the
multiple-choice values are dimensionless real readouts.  Figure observations,
geometrical relations, physical branch conditions, governing optics, and the
requested answer are kept separate.
-/

namespace PhyXMiniProblems.ProblemPhyxMini0074

noncomputable section

/-! ## Angle units and diagram labels -/

/-- Convert a degree readout to Mathlib's angle type. -/
noncomputable def angleFromDegrees (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- Refractive index is dimensionless in Physlib's dimension system. -/
def refractiveIndexDimension : Dimension := 1

/-- The Cartesian plane containing the triangular prism cross-section. -/
abbrev DiagramPlane := ℝ × ℝ

/-- The three directed portions of the depicted light ray. -/
inductive RaySegment where
  | incoming
  | insidePrism
  | outgoing
  deriving DecidableEq, Repr

/-- The three faces of the equilateral triangular cross-section. -/
inductive PrismFace where
  | entryFace
  | exitFace
  | base
  deriving DecidableEq, Repr

/-- The two refracting interfaces crossed by the ray. -/
inductive RefractingInterface where
  | entryFace
  | exitFace
  deriving DecidableEq, Repr

/-- The homogeneous optical media traversed by the ray. -/
inductive OpticalMedium where
  | air
  | prism
  deriving DecidableEq, Repr

/-- The three angle labels visible in the primary image. -/
inductive FigureAngleLabel where
  | apexAlpha
  | entryBeta
  | exitBeta
  deriving DecidableEq, Repr

/-- Incident medium along the propagation direction at each interface. -/
def incidentMedium : RefractingInterface → OpticalMedium
  | .entryFace => .air
  | .exitFace => .prism

/-- Transmitted medium along the propagation direction at each interface. -/
def transmittedMedium : RefractingInterface → OpticalMedium
  | .entryFace => .prism
  | .exitFace => .air

/-! ## Physical setup and primary-image readouts -/

/--
Physical quantities and labelled geometry carried by the prism diagram.

At each interface, incidence and refraction angles are measured from the
depicted normal on the incident and transmitted sides respectively.  A
`Module.Ray` records a nonzero direction modulo positive rescaling, so equality
of the internal-ray and base directions faithfully expresses the oriented
parallelism shown in the figure.
-/
structure EquilateralPrismDiagram where
  /-- Dimensionless real readout of each homogeneous medium's refractive index. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Angle between the incident ray and the interface normal. -/
  incidenceAngle : RefractingInterface → Real.Angle
  /-- Angle between the transmitted ray and the interface normal. -/
  refractionAngle : RefractingInterface → Real.Angle
  /-- Physical angle denoted by each label in the figure. -/
  angleForLabel : FigureAngleLabel → Real.Angle
  /-- Smaller interior angle between two prism faces. -/
  angleBetweenFaces : PrismFace → PrismFace → Real.Angle
  /-- Oriented ray of each portion of the light path. -/
  rayDirection : RaySegment → Module.Ray ℝ DiagramPlane
  /-- Oriented tangent ray of each prism face. -/
  faceDirection : PrismFace → Module.Ray ℝ DiagramPlane
  /-- Normal at each refracting face, oriented toward the transmitted medium. -/
  interfaceNormalDirection :
    RefractingInterface → Module.Ray ℝ DiagramPlane
  /-- Whether a named ray segment is visible in the primary image. -/
  raySegmentDepicted : RaySegment → Prop
  /-- Whether a named prism face is present in the cross-section. -/
  faceDepicted : PrismFace → Prop
  /-- Whether the dashed normal is visible at an interface. -/
  interfaceNormalDepicted : RefractingInterface → Prop

/--
Primary-image and laboratory readouts.  These premises record the equilateral
prism, the meanings of `α` and the two `β` labels, the measured `52.2°`
external angles, and the air-index calibration.  They do not assign a value to
the prism's refractive index.
-/
structure MatchesPrimaryFigure (diagram : EquilateralPrismDiagram) : Prop where
  allRaySegmentsDepicted : ∀ ray, diagram.raySegmentDepicted ray
  allFacesDepicted : ∀ face, diagram.faceDepicted face
  bothInterfaceNormalsDepicted :
    ∀ interface, diagram.interfaceNormalDepicted interface
  alphaLabelsApex :
    diagram.angleForLabel .apexAlpha =
      diagram.angleBetweenFaces .entryFace .exitFace
  equilateralApexReadout :
    diagram.angleForLabel .apexAlpha = angleFromDegrees 60
  equilateralEntryBaseAngle :
    diagram.angleBetweenFaces .entryFace .base = angleFromDegrees 60
  equilateralExitBaseAngle :
    diagram.angleBetweenFaces .exitFace .base = angleFromDegrees 60
  entryBetaLabelsIncidence :
    diagram.angleForLabel .entryBeta =
      diagram.incidenceAngle .entryFace
  exitBetaLabelsEmergence :
    diagram.angleForLabel .exitBeta =
      diagram.refractionAngle .exitFace
  measuredEntryBeta :
    diagram.angleForLabel .entryBeta = angleFromDegrees 52.2
  measuredExitBeta :
    diagram.angleForLabel .exitBeta = angleFromDegrees 52.2
  airIndexCalibration : diagram.refractiveIndex .air = 1

/-- An incidence or refraction angle is on the acute physical branch shown in
the ray diagram. -/
def IsPhysicalRayAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal < Real.pi / 2

/-- Positivity and branch conditions for the elementary optical model. -/
structure HasPhysicalOpticalParameters
    (diagram : EquilateralPrismDiagram) : Prop where
  refractiveIndexPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  incidenceAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.incidenceAngle interface)
  refractionAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.refractionAngle interface)

/-! ## Governing prism geometry and optics -/

/--
Geometric relations induced by the internal ray being parallel to the base of
an equilateral prism.  The two internal normal angles are equal, and the
standard prism-angle relation says that their sum is the apex angle.  No field
fixes a refractive index or selects an answer choice.
-/
structure MatchesParallelBaseRayGeometry
    (diagram : EquilateralPrismDiagram) : Prop where
  internalRayParallelToBase :
    diagram.rayDirection .insidePrism = diagram.faceDirection .base
  internalAnglesEqual :
    diagram.refractionAngle .entryFace =
      diagram.incidenceAngle .exitFace
  internalAnglesSumToApex :
    diagram.refractionAngle .entryFace +
        diagram.incidenceAngle .exitFace =
      diagram.angleForLabel .apexAlpha

/--
For the acute physical branch, equal internal angles whose sum is the `60°`
apex angle are both `30°`.  This isolates the figure-derived geometry from the
subsequent application of Snell's law.
-/
theorem internalInterfaceAnglesAreThirtyDegrees
    (diagram : EquilateralPrismDiagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hParameters : HasPhysicalOpticalParameters diagram)
    (hGeometry : MatchesParallelBaseRayGeometry diagram) :
    diagram.refractionAngle .entryFace = angleFromDegrees 30 ∧
      diagram.incidenceAngle .exitFace = angleFromDegrees 30 := by
  have hxPhysical := hParameters.refractionAnglesPhysical .entryFace
  have hxAbs :
      |(diagram.refractionAngle .entryFace).toReal| < Real.pi / 2 := by
    rw [abs_of_nonneg hxPhysical.1]
    exact hxPhysical.2
  have hThirtyToReal :
      (angleFromDegrees 30).toReal = Real.pi / 6 := by
    change ((↑(30 * Real.pi / 180) : Real.Angle).toReal = Real.pi / 6)
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have hThirtyAbs :
      |(angleFromDegrees 30).toReal| < Real.pi / 2 := by
    rw [hThirtyToReal, abs_of_pos (by positivity : 0 < Real.pi / 6)]
    nlinarith [Real.pi_pos]
  have hdouble :
      (2 : ℕ) • diagram.refractionAngle .entryFace =
        (2 : ℕ) • angleFromDegrees 30 := by
    rw [two_nsmul, two_nsmul]
    calc
      diagram.refractionAngle .entryFace +
            diagram.refractionAngle .entryFace =
          diagram.refractionAngle .entryFace +
            diagram.incidenceAngle .exitFace := by
              rw [hGeometry.internalAnglesEqual]
      _ = diagram.angleForLabel .apexAlpha :=
        hGeometry.internalAnglesSumToApex
      _ = angleFromDegrees 60 := hFigure.equilateralApexReadout
      _ = angleFromDegrees 30 + angleFromDegrees 30 := by
        simp only [angleFromDegrees, ← Real.Angle.coe_add]
        congr 1
        ring
  have hEntry :
      diagram.refractionAngle .entryFace = angleFromDegrees 30 :=
    (Real.Angle.two_nsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
      hxAbs hThirtyAbs).mp hdouble
  refine ⟨hEntry, ?_⟩
  rw [← hGeometry.internalAnglesEqual]
  exact hEntry

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one labelled interface. -/
def SnellsLawAt
    (diagram : EquilateralPrismDiagram)
    (interface : RefractingInterface) : Prop :=
  diagram.refractiveIndex (incidentMedium interface) *
      Real.Angle.sin (diagram.incidenceAngle interface) =
    diagram.refractiveIndex (transmittedMedium interface) *
      Real.Angle.sin (diagram.refractionAngle interface)

/-- The depicted light ray obeys Snell's law at both prism faces. -/
structure ObeysSnellsLaw (diagram : EquilateralPrismDiagram) : Prop where
  atInterface : ∀ interface, SnellsLawAt diagram interface

/-! ## Multiple-choice target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless refractive-index readout printed for each answer choice. -/
def AnswerChoice.refractiveIndexReadout : AnswerChoice → ℝ
  | .A => 1.47
  | .B => 2.26
  | .C => 1.58
  | .D => 1.95

/-- Dataset metadata: the recorded answer label is C.  This is not used as a
premise of the target theorem. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A physical index rounds to the displayed value to the nearest hundredth. -/
def RoundsToNearestHundredth
    (actualIndex displayedIndex : ℝ) : Prop :=
  |actualIndex - displayedIndex| < 1 / 200

/-- A displayed choice is strictly nearer to the physical index than every
other displayed choice. -/
def IsNearestAnswerChoice
    (actualIndex : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |actualIndex - choice.refractiveIndexReadout| <
        |actualIndex - otherChoice.refractiveIndexReadout|

/--
**Physics formalization target
(`thm:physics:phyx_mini_0074:target`).**

For the equilateral prism whose internal ray is parallel to the base and whose
external angle is measured as `β = 52.2°`, Snell's law gives the exact sine
ratio below.  Its value rounds to `1.58` and is uniquely closest to answer C.
-/
theorem prismRefractiveIndexIsAnswerC
    (diagram : EquilateralPrismDiagram)
    (hFigure : MatchesPrimaryFigure diagram)
    (hParameters : HasPhysicalOpticalParameters diagram)
    (hGeometry : MatchesParallelBaseRayGeometry diagram)
    (hSnell : ObeysSnellsLaw diagram) :
    diagram.refractiveIndex .prism =
        Real.Angle.sin (angleFromDegrees 52.2) /
          Real.Angle.sin (angleFromDegrees 30) ∧
      RoundsToNearestHundredth
        (diagram.refractiveIndex .prism)
        AnswerChoice.C.refractiveIndexReadout ∧
      IsNearestAnswerChoice
        (diagram.refractiveIndex .prism) .C := by
  obtain ⟨hEntryRefraction, _⟩ :=
    internalInterfaceAnglesAreThirtyDegrees
      diagram hFigure hParameters hGeometry
  have hEntryIncidence :
      diagram.incidenceAngle .entryFace = angleFromDegrees 52.2 := by
    calc
      diagram.incidenceAngle .entryFace =
          diagram.angleForLabel .entryBeta :=
        hFigure.entryBetaLabelsIncidence.symm
      _ = angleFromDegrees 52.2 := hFigure.measuredEntryBeta
  have hsinThirty :
      Real.Angle.sin (angleFromDegrees 30) = (1 : ℝ) / 2 := by
    simp only [angleFromDegrees, Real.Angle.sin_coe]
    rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring,
      Real.sin_pi_div_six]
  have hSnellEntry := hSnell.atInterface .entryFace
  simp only [SnellsLawAt, incidentMedium, transmittedMedium] at hSnellEntry
  rw [hFigure.airIndexCalibration, hEntryIncidence, hEntryRefraction,
    hsinThirty, one_mul] at hSnellEntry
  have hIndex :
      diagram.refractiveIndex .prism =
        Real.Angle.sin (angleFromDegrees 52.2) /
          Real.Angle.sin (angleFromDegrees 30) := by
    rw [hsinThirty]
    norm_num
    nlinarith only [hSnellEntry]
  have hsinFiftyTwo :
      Real.Angle.sin (angleFromDegrees 52.2) =
        Real.sin (29 * Real.pi / 100) := by
    simp only [angleFromDegrees, Real.Angle.sin_coe]
    congr 1
    norm_num
    ring
  have hIndexSin :
      diagram.refractiveIndex .prism =
        2 * Real.sin (29 * Real.pi / 100) := by
    rw [hIndex, hsinFiftyTwo, hsinThirty]
    ring

  have hpiBounds :
      (31 : ℝ) / 10 < Real.pi ∧ Real.pi < 16 / 5 := by
    have hsqrtTwoNonneg :
        0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrtTwoSq :
        (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrtTwoLower :
        (1414 : ℝ) / 1000 < Real.sqrt 2 := by
      nlinarith only [hsqrtTwoNonneg, hsqrtTwoSq,
        sq_nonneg (Real.sqrt 2 - 1414 / 1000)]
    have hsqrtTwoUpper :
        Real.sqrt 2 < (1415 : ℝ) / 1000 := by
      nlinarith only [hsqrtTwoNonneg, hsqrtTwoSq,
        sq_nonneg (Real.sqrt 2 - 1415 / 1000)]
    have hsinPiEightNonneg :
        0 ≤ Real.sin (Real.pi / 8) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · nlinarith only [Real.pi_pos]
    have hsinPiEightSq :
        Real.sin (Real.pi / 8) ^ 2 =
          1 / 2 - Real.sqrt 2 / 4 := by
      rw [Real.sin_sq_eq_half_sub,
        show 2 * (Real.pi / 8) = Real.pi / 4 by ring,
        Real.cos_pi_div_four]
      ring
    have hsinPiEightLower :
        (382 : ℝ) / 1000 < Real.sin (Real.pi / 8) := by
      nlinarith only [hsinPiEightNonneg, hsinPiEightSq,
        hsqrtTwoUpper,
        sq_nonneg (Real.sin (Real.pi / 8) - 382 / 1000)]
    have hsinPiEightUpper :
        Real.sin (Real.pi / 8) < (383 : ℝ) / 1000 := by
      nlinarith only [hsinPiEightNonneg, hsinPiEightSq,
        hsqrtTwoLower,
        sq_nonneg (Real.sin (Real.pi / 8) - 383 / 1000)]
    have hxNonneg : 0 ≤ Real.pi / 8 := by
      positivity
    have hxUpper : Real.pi / 8 ≤ (1 : ℝ) / 2 := by
      nlinarith only [Real.pi_le_four]
    have hxAbs : |Real.pi / 8| ≤ 1 := by
      rw [abs_of_nonneg hxNonneg]
      linarith only [hxUpper]
    have hsinBound := Real.sin_bound hxAbs
    rw [abs_of_nonneg hxNonneg] at hsinBound
    rcases abs_le.mp hsinBound with
      ⟨hsinBoundLower, hsinBoundUpper⟩
    constructor
    · by_contra h
      have hxLe :
          Real.pi / 8 ≤ (31 : ℝ) / 80 := by
        linarith only [h]
      have hx3Le :
          (Real.pi / 8) ^ 3 ≤ ((31 : ℝ) / 80) ^ 3 :=
        pow_le_pow_left₀ hxNonneg hxLe 3
      have hx4Le :
          (Real.pi / 8) ^ 4 ≤ ((31 : ℝ) / 80) ^ 4 :=
        pow_le_pow_left₀ hxNonneg hxLe 4
      have hpoly :
          Real.pi / 8 - (Real.pi / 8) ^ 3 / 6 ≤
            (31 : ℝ) / 80 - ((31 : ℝ) / 80) ^ 3 / 6 := by
        have hfactor :
            0 ≤ ((31 : ℝ) / 80 - Real.pi / 8) *
              (1 - (((31 : ℝ) / 80) ^ 2 +
                (31 / 80) * (Real.pi / 8) +
                (Real.pi / 8) ^ 2) / 6) := by
          apply mul_nonneg
          · linarith
          · nlinarith only [hxNonneg, hxLe,
              sq_nonneg ((31 : ℝ) / 80 - Real.pi / 8)]
        nlinarith only [hfactor]
      norm_num at hsinBoundUpper hsinPiEightLower ⊢
      nlinarith only [hsinBoundUpper, hsinPiEightLower,
        hx4Le, hpoly]
    · by_contra h
      have hxGe :
          (2 : ℝ) / 5 ≤ Real.pi / 8 := by
        linarith only [h]
      have hpoly :
          (2 : ℝ) / 5 - ((2 : ℝ) / 5) ^ 3 / 6 ≤
            Real.pi / 8 - (Real.pi / 8) ^ 3 / 6 := by
        have hfactor :
            0 ≤ (Real.pi / 8 - (2 : ℝ) / 5) *
              (1 - ((Real.pi / 8) ^ 2 +
                (Real.pi / 8) * (2 / 5) +
                ((2 : ℝ) / 5) ^ 2) / 6) := by
          apply mul_nonneg
          · linarith
          · nlinarith only [hxNonneg, hxUpper, hxGe,
              sq_nonneg (Real.pi / 8 - (2 : ℝ) / 5)]
        nlinarith only [hfactor]
      have hx4Le :
          (Real.pi / 8) ^ 4 ≤ ((1 : ℝ) / 2) ^ 4 :=
        pow_le_pow_left₀ hxNonneg hxUpper 4
      norm_num at hsinBoundLower hsinPiEightUpper ⊢
      nlinarith only [hsinBoundLower, hsinPiEightUpper,
        hx4Le, hpoly]

  have hsinBounds :
      (63 : ℝ) / 80 < Real.sin (29 * Real.pi / 100) ∧
        Real.sin (29 * Real.pi / 100) < (317 : ℝ) / 400 := by
    let y : ℝ := 13 * Real.pi / 300
    have hyLower : (67 : ℝ) / 500 < y := by
      dsimp [y]
      nlinarith only [hpiBounds.1]
    have hyUpper : y < (139 : ℝ) / 1000 := by
      dsimp [y]
      nlinarith only [hpiBounds.2]
    have hyNonneg : 0 ≤ y :=
      hyLower.le.trans' (by norm_num)
    have hyAbs : |y| ≤ 1 := by
      rw [abs_of_nonneg hyNonneg]
      linarith only [hyUpper]
    have hy2Lower :
        ((67 : ℝ) / 500) ^ 2 < y ^ 2 :=
      pow_lt_pow_left₀ hyLower (by norm_num) (by norm_num)
    have hy2Upper :
        y ^ 2 < ((139 : ℝ) / 1000) ^ 2 :=
      pow_lt_pow_left₀ hyUpper hyNonneg (by norm_num)
    have hy3Lower :
        ((67 : ℝ) / 500) ^ 3 < y ^ 3 :=
      pow_lt_pow_left₀ hyLower (by norm_num) (by norm_num)
    have hy3Upper :
        y ^ 3 < ((139 : ℝ) / 1000) ^ 3 :=
      pow_lt_pow_left₀ hyUpper hyNonneg (by norm_num)
    have hy4Upper :
        y ^ 4 < ((139 : ℝ) / 1000) ^ 4 :=
      pow_lt_pow_left₀ hyUpper hyNonneg (by norm_num)
    have hsinBound := Real.sin_bound hyAbs
    rw [abs_of_nonneg hyNonneg] at hsinBound
    rcases abs_le.mp hsinBound with
      ⟨hsinBoundLower, hsinBoundUpper⟩
    have hsinLower :
        (267 : ℝ) / 2000 < Real.sin y := by
      nlinarith only [hsinBoundLower, hyLower,
        hy3Upper, hy4Upper]
    have hsinUpper :
        Real.sin y < (139 : ℝ) / 1000 := by
      nlinarith only [hsinBoundUpper, hyUpper,
        hy3Lower, hy4Upper]
    have hcosBound := Real.cos_bound hyAbs
    rw [abs_of_nonneg hyNonneg] at hcosBound
    rcases abs_le.mp hcosBound with
      ⟨hcosBoundLower, hcosBoundUpper⟩
    have hcosLower :
        (99 : ℝ) / 100 < Real.cos y := by
      nlinarith only [hcosBoundLower, hy2Upper, hy4Upper]
    have hcosUpper :
        Real.cos y < (1983 : ℝ) / 2000 := by
      nlinarith only [hcosBoundUpper, hy2Lower, hy4Upper]
    have hsqrtNonneg :
        0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hsqrtSq :
        (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrtLower :
        (433 : ℝ) / 250 < Real.sqrt 3 := by
      nlinarith only [hsqrtNonneg, hsqrtSq,
        sq_nonneg (Real.sqrt 3 - 433 / 250)]
    have hsqrtUpper :
        Real.sqrt 3 < (1733 : ℝ) / 1000 := by
      nlinarith only [hsqrtNonneg, hsqrtSq,
        sq_nonneg (Real.sqrt 3 - 1733 / 1000)]
    have hprodLower :
        (433 / 250 : ℝ) * (99 / 100) <
          Real.sqrt 3 * Real.cos y :=
      mul_lt_mul hsqrtLower hcosLower.le
        (by norm_num) hsqrtNonneg
    have hprodUpper :
        Real.sqrt 3 * Real.cos y <
          (1733 / 1000 : ℝ) * (1983 / 2000) :=
      mul_lt_mul hsqrtUpper hcosUpper.le
        (by linarith) (by norm_num)
    have hsinIdentity :
        Real.sin (29 * Real.pi / 100) =
          Real.sqrt 3 / 2 * Real.cos y -
            (1 / 2) * Real.sin y := by
      rw [show (29 : ℝ) * Real.pi / 100 =
          Real.pi / 3 - y by
        dsimp [y]
        ring]
      rw [Real.sin_sub, Real.sin_pi_div_three,
        Real.cos_pi_div_three]
    rw [hsinIdentity]
    constructor
    · nlinarith only [hprodLower, hsinUpper]
    · nlinarith only [hprodUpper, hsinLower]

  have hIndexLower :
      (315 : ℝ) / 200 < diagram.refractiveIndex .prism := by
    rw [hIndexSin]
    nlinarith only [hsinBounds.1]
  have hIndexUpper :
      diagram.refractiveIndex .prism < (317 : ℝ) / 200 := by
    rw [hIndexSin]
    nlinarith only [hsinBounds.2]
  have hRounds :
      RoundsToNearestHundredth
        (diagram.refractiveIndex .prism)
        AnswerChoice.C.refractiveIndexReadout := by
    simp only [RoundsToNearestHundredth,
      AnswerChoice.refractiveIndexReadout]
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  refine ⟨hIndex, hRounds, ?_⟩
  intro otherChoice hOther
  cases otherChoice with
  | A =>
      simp only [AnswerChoice.refractiveIndexReadout]
      norm_num
      rw [abs_of_nonneg (show
        0 ≤ diagram.refractiveIndex .prism - 147 / 100 by
          linarith only [hIndexLower])]
      have hError := hRounds
      simp only [RoundsToNearestHundredth,
        AnswerChoice.refractiveIndexReadout] at hError
      norm_num at hError ⊢
      linarith only [hError, hIndexLower]
  | B =>
      simp only [AnswerChoice.refractiveIndexReadout]
      norm_num
      rw [abs_of_nonpos (show
        diagram.refractiveIndex .prism - 113 / 50 ≤ 0 by
          linarith only [hIndexUpper])]
      have hError := hRounds
      simp only [RoundsToNearestHundredth,
        AnswerChoice.refractiveIndexReadout] at hError
      norm_num at hError ⊢
      linarith only [hError, hIndexUpper]
  | C =>
      exact (hOther rfl).elim
  | D =>
      simp only [AnswerChoice.refractiveIndexReadout]
      norm_num
      rw [abs_of_nonpos (show
        diagram.refractiveIndex .prism - 39 / 20 ≤ 0 by
          linarith only [hIndexUpper])]
      have hError := hRounds
      simp only [RoundsToNearestHundredth,
        AnswerChoice.refractiveIndexReadout] at hError
      norm_num at hError ⊢
      linarith only [hError, hIndexUpper]

end

end PhyXMiniProblems.ProblemPhyxMini0074
