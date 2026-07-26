import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Tibia tension of an insect hanging below a rod

An insect of mass `m` hangs below a horizontal rod.  Each of its six tibiae
has the same tension magnitude and makes the angle `theta = 40 degrees` with
the horizontal leg section nearest the body.  Static vertical balance gives
`6 T sin(theta) = W`.

Mass, acceleration, weight, tension, and vertical-support magnitudes use
Physlib's unit-independent `Dimensionful (WithDim ...)` representation.
Real numbers occur only as coherent-unit readouts, radian angles,
dimensionless ratios, and displayed answer values.

Assumption/target boundary:

* `MatchesProblemData` contains the horizontal-rod datum, the forty-degree
  angle, the horizontal proximal sections, and equality of the six tensions.
* `MatchesPrimaryFigure` contains only the labelled components and qualitative
  geometry visible in the supplied raster.
* `SatisfiesHangingStaticsLaws` states weight, force-component, and static
  vertical-equilibrium laws.
* There are no previous-part results.
* The exact tension-to-weight ratio and its rounded value `0.26` occur only in
  conclusions and in the displayed-answer table, never in a premise.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0758

open Dimension
open scoped BigOperators

/-! ## Dimensionful physical quantities and scalar readouts -/

/-- Acceleration has physical dimension `L T^-2`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T^-2`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude, used for weight, tension, and support. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a nonnegative dimensionful scalar in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of the insect's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI mass

/-- Metres-per-second-squared readout of a physical acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI acceleration

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  nonnegativeReadout UnitChoices.SI force

/-- Convert an angle stated in degrees to the radian argument used by `Real.sin`. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Six legs and primary-figure vocabulary -/

/-- The insect's six individually identifiable legs. -/
inductive InsectLeg where
  | leftFore
  | leftMiddle
  | leftHind
  | rightFore
  | rightMiddle
  | rightHind
  deriving DecidableEq, Fintype, Repr

/-- Left and right sides in the front-view schematic. -/
inductive BodySide where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Orientation of a rod or a leg segment in the schematic plane. -/
inductive SegmentOrientation where
  | horizontal
  | inclined
  deriving DecidableEq, Repr

/-- Named graphical features visible in the supplied primary image. -/
inductive FigureFeature where
  | rod
  | tibia
  | legJoint
  | thetaArc
  | proximalLegSection
  | insectBody
  deriving DecidableEq, Fintype, Repr

/-- Literal text or symbol labels printed in the primary image. -/
inductive FigureLabel where
  | rod
  | tibia
  | legJoint
  | theta
  deriving DecidableEq, Fintype, Repr

/-- The graphical feature to which each printed label is attached. -/
def expectedLabelTarget : FigureLabel → FigureFeature
  | .rod => .rod
  | .tibia => .tibia
  | .legJoint => .legJoint
  | .theta => .thetaArc

/-- Qualitative labels and incidences transcribed from image `758.png`. -/
structure SuppliedHangingInsectFigure where
  showsFeature : FigureFeature → Bool
  labelTarget : FigureLabel → FigureFeature
  tibiaRunsFromJointToRod : BodySide → Bool
  proximalSectionRunsFromBodyToJoint : BodySide → Bool
  tibiaInclinesUpwardTowardRod : BodySide → Bool
  thetaArcSide : BodySide
  tibiaTextSide : BodySide

/-!
Independent physical quantities of the hanging insect.  In particular, the
tibia tensions and the insect weight are not defined from the requested
ratio.  `verticalSupportMagnitude` is the upward component transmitted by
each tibia to the insect-plus-legs free body.
-/
structure HangingInsectSetup where
  insectMass : MassQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  weightMagnitude : ForceMagnitude
  tibiaTensionMagnitude : InsectLeg → ForceMagnitude
  verticalSupportMagnitude : InsectLeg → ForceMagnitude
  tibiaAngleRadians : ℝ
  rodOrientation : SegmentOrientation
  proximalSectionOrientation : InsectLeg → SegmentOrientation
  figure : SuppliedHangingInsectFigure

/-! ## Problem data, figure readouts, and governing laws -/

/-!
Numerical and categorical data stated in the prose.  Equal tension is stated
relationally across independently represented legs; no tension-to-weight
ratio is supplied here.
-/
structure MatchesProblemData (setup : HangingInsectSetup) : Prop where
  rodIsHorizontal : setup.rodOrientation = .horizontal
  thetaIsFortyDegrees :
    setup.tibiaAngleRadians = degreesToRadians 40
  proximalSectionsAreHorizontal :
    ∀ leg, setup.proximalSectionOrientation leg = .horizontal
  allTibiaTensionsEqual :
    ∀ first second,
      setup.tibiaTensionMagnitude first =
        setup.tibiaTensionMagnitude second

/-!
Primary-image evidence.  The angle arc is on the left representative leg,
whereas the word `Tibia` is printed on the right; both tibiae incline from a
leg joint upward to the rod.  These are figure readouts, not force laws.
-/
structure MatchesPrimaryFigure (setup : HangingInsectSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.showsFeature feature = true
  labelsAttachedToExpectedFeatures :
    ∀ label, setup.figure.labelTarget label = expectedLabelTarget label
  representativeTibiaeJoinRod :
    ∀ side, setup.figure.tibiaRunsFromJointToRod side = true
  representativeProximalSectionsJoinBody :
    ∀ side, setup.figure.proximalSectionRunsFromBodyToJoint side = true
  representativeTibiaeInclineUpward :
    ∀ side, setup.figure.tibiaInclinesUpwardTowardRod side = true
  thetaArcDrawnOnLeft : setup.figure.thetaArcSide = .left
  tibiaTextDrawnOnRight : setup.figure.tibiaTextSide = .right

/-- Positivity and nondegeneracy conditions for the hanging configuration. -/
structure HasPhysicalHangingParameters
    (setup : HangingInsectSetup) : Prop where
  massPositive : 0 < massInKilograms setup.insectMass
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  weightPositive : 0 < forceInNewtons setup.weightMagnitude
  tibiaTensionsPositive :
    ∀ leg, 0 < forceInNewtons (setup.tibiaTensionMagnitude leg)
  thetaPositive : 0 < setup.tibiaAngleRadians
  thetaAcute : setup.tibiaAngleRadians < Real.pi / 2

/-!
The governing mechanics laws, stated in every coherent unit system:

* the weight magnitude is `m g`;
* the upward component of each inclined tibia tension is `T sin(theta)`; and
* static vertical balance makes the sum of those six components equal the
  insect's weight.

No target ratio or displayed answer value appears in this structure.
-/
structure SatisfiesHangingStaticsLaws
    (setup : HangingInsectSetup) : Prop where
  weightLaw :
    ∀ units : UnitChoices,
      nonnegativeReadout units setup.weightMagnitude =
        nonnegativeReadout units setup.insectMass *
          nonnegativeReadout units
            setup.gravitationalAccelerationMagnitude
  tibiaVerticalComponentLaw :
    ∀ (units : UnitChoices) (leg : InsectLeg),
      nonnegativeReadout units (setup.verticalSupportMagnitude leg) =
        nonnegativeReadout units (setup.tibiaTensionMagnitude leg) *
          Real.sin setup.tibiaAngleRadians
  staticVerticalEquilibrium :
    ∀ units : UnitChoices,
      (∑ leg : InsectLeg,
          nonnegativeReadout units (setup.verticalSupportMagnitude leg)) =
        nonnegativeReadout units setup.weightMagnitude

/-! ## Dimensionless ratio, displayed answers, and target -/

/-- Tension in one named tibia divided by the insect's weight. -/
def tibiaTensionToWeightRatio
    (setup : HangingInsectSetup) (leg : InsectLeg) : ℝ :=
  forceInNewtons (setup.tibiaTensionMagnitude leg) /
    forceInNewtons setup.weightMagnitude

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless ratio printed beside each displayed answer label. -/
def displayedRatio : AnswerChoice → ℝ
  | .A => 37 / 50
  | .B => 23 / 50
  | .C => 13 / 50
  | .D => 27 / 50

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A calculated ratio agrees with a two-decimal displayed answer when it lies
within half of one hundredth of that displayed value.
-/
def MatchesDisplayedRatioAnswer
    (setup : HangingInsectSetup) (choice : AnswerChoice) : Prop :=
  ∀ leg : InsectLeg,
    |tibiaTensionToWeightRatio setup leg - displayedRatio choice| ≤
      1 / 200

/-!
Six equal inclined tibia tensions in vertical equilibrium give the exact
ratio `T/W = 1 / (6 sin(40 degrees))` for every leg.
-/
lemma tibiaTensionToWeightRatio_exact
    (setup : HangingInsectSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalHangingParameters setup)
    (_laws : SatisfiesHangingStaticsLaws setup) :
    ∀ leg : InsectLeg,
      tibiaTensionToWeightRatio setup leg =
        1 / (6 * Real.sin (degreesToRadians 40)) := by
  intro leg
  have hTension (other : InsectLeg) :
      nonnegativeReadout UnitChoices.SI
          (setup.tibiaTensionMagnitude other) =
        nonnegativeReadout UnitChoices.SI
          (setup.tibiaTensionMagnitude leg) := by
    exact congrArg (fun force => nonnegativeReadout UnitChoices.SI force)
      (_data.allTibiaTensionsEqual other leg)
  have hBalance := _laws.staticVerticalEquilibrium UnitChoices.SI
  simp_rw [_laws.tibiaVerticalComponentLaw UnitChoices.SI] at hBalance
  simp_rw [hTension] at hBalance
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hBalance
  have hCard : Fintype.card InsectLeg = 6 := by decide
  rw [hCard] at hBalance
  rw [_data.thetaIsFortyDegrees] at hBalance
  have hWeightPositive :
      0 < nonnegativeReadout UnitChoices.SI setup.weightMagnitude := by
    exact _physical.weightPositive
  have hTensionPositive :
      0 < nonnegativeReadout UnitChoices.SI
        (setup.tibiaTensionMagnitude leg) := by
    exact _physical.tibiaTensionsPositive leg
  have hSinPositive : 0 < Real.sin (degreesToRadians 40) := by
    by_contra h
    have hSinNonpositive : Real.sin (degreesToRadians 40) ≤ 0 :=
      le_of_not_gt h
    have hProductNonpositive :
        nonnegativeReadout UnitChoices.SI
            (setup.tibiaTensionMagnitude leg) *
          Real.sin (degreesToRadians 40) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hTensionPositive.le hSinNonpositive
    nlinarith
  unfold tibiaTensionToWeightRatio forceInNewtons
  apply (div_eq_div_iff hWeightPositive.ne' (mul_ne_zero (by norm_num)
    hSinPositive.ne')).2
  norm_num
  convert hBalance using 1
  all_goals ring

/-!
The exact statics ratio rounds to `0.26`, hence agrees with recorded answer C.

Blueprint: `thm:physics:phyx_mini_0758:target`.
-/
theorem problem_phyx_mini_0758
    (setup : HangingInsectSetup)
    (_data : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalHangingParameters setup)
    (_laws : SatisfiesHangingStaticsLaws setup) :
    (∀ leg : InsectLeg,
      tibiaTensionToWeightRatio setup leg =
        1 / (6 * Real.sin (degreesToRadians 40))) ∧
      MatchesDisplayedRatioAnswer setup recordedAnswerChoice := by
  have hExact :=
    tibiaTensionToWeightRatio_exact setup _data _physical _laws
  refine ⟨hExact, ?_⟩
  have hPiLower : (31 / 10 : ℝ) < Real.pi := by
    have hSinAtLowerTest :
        Real.sin (31 / 60 : ℝ) < (1 / 2 : ℝ) := by
      have h := Real.sin_bound (x := (31 / 60 : ℝ)) (by norm_num)
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 60)] at h
      nlinarith [le_abs_self
        (Real.sin (31 / 60 : ℝ) -
          ((31 / 60 : ℝ) - (31 / 60 : ℝ) ^ 3 / 6))]
    by_contra hPi
    have hPiLe : Real.pi ≤ (31 / 10 : ℝ) := le_of_not_gt hPi
    have hMonotone :
        Real.sin (Real.pi / 6) ≤ Real.sin (31 / 60 : ℝ) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.two_le_pi]
      · nlinarith
    rw [Real.sin_pi_div_six] at hMonotone
    linarith
  have hPiUpper : Real.pi < (63 / 20 : ℝ) := by
    have hSinSmall :
        (2592 / 10000 : ℝ) < Real.sin (21 / 80 : ℝ) := by
      have h := Real.sin_bound (x := (21 / 80 : ℝ)) (by norm_num)
      have hLower := neg_le_of_abs_le h
      norm_num at hLower ⊢
      linarith
    have hCosSmall :
        (96529 / 100000 : ℝ) < Real.cos (21 / 80 : ℝ) := by
      have h := Real.cos_bound (x := (21 / 80 : ℝ)) (by norm_num)
      have hLower := neg_le_of_abs_le h
      norm_num at hLower ⊢
      linarith
    have hProduct :
        (1 / 4 : ℝ) <
          Real.sin (21 / 80 : ℝ) * Real.cos (21 / 80 : ℝ) := by
      have h₁ := mul_pos (sub_pos.mpr hSinSmall)
        (lt_trans (by norm_num) hCosSmall)
      have h₂ := mul_pos (by norm_num : (0 : ℝ) < 2592 / 10000)
        (sub_pos.mpr hCosSmall)
      nlinarith
    have hSinDouble : (1 / 2 : ℝ) < Real.sin (21 / 40 : ℝ) := by
      rw [show (21 / 40 : ℝ) = 2 * (21 / 80 : ℝ) by norm_num,
        Real.sin_two_mul]
      nlinarith
    by_contra hPi
    have hPiGe : (63 / 20 : ℝ) ≤ Real.pi := le_of_not_gt hPi
    have hMonotone :
        Real.sin (21 / 40 : ℝ) ≤ Real.sin (Real.pi / 6) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.one_le_pi_div_two]
      · nlinarith [Real.pi_pos]
      · nlinarith
    rw [Real.sin_pi_div_six] at hMonotone
    linarith
  let x : ℝ := Real.pi / 9
  have hxPositive : 0 < x := by
    dsimp [x]
    positivity
  have hxLower : (31 / 90 : ℝ) < x := by
    dsimp [x]
    nlinarith
  have hxUpper : x < (7 / 20 : ℝ) := by
    dsimp [x]
    nlinarith
  have hxAbsLeOne : |x| ≤ (1 : ℝ) := by
    rw [abs_of_pos hxPositive]
    linarith
  have hxSquareLower : (31 / 90 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hxLower.le 2
  have hxSquareUpper : x ^ 2 ≤ (7 / 20 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hxPositive.le hxUpper.le 2
  have hxCubeLower : (31 / 90 : ℝ) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hxLower.le 3
  have hxCubeUpper : x ^ 3 ≤ (7 / 20 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hxPositive.le hxUpper.le 3
  have hxFourthUpper : x ^ 4 ≤ (7 / 20 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hxPositive.le hxUpper.le 4
  have hSinTaylor := Real.sin_bound hxAbsLeOne
  have hCosTaylor := Real.cos_bound hxAbsLeOne
  rw [abs_of_pos hxPositive] at hSinTaylor hCosTaylor
  rcases abs_le.mp hSinTaylor with
    ⟨hSinTaylorLower, hSinTaylorUpper⟩
  rcases abs_le.mp hCosTaylor with
    ⟨hCosTaylorLower, hCosTaylorUpper⟩
  have hSinLower : (673 / 2000 : ℝ) < Real.sin x := by
    nlinarith
  have hSinUpper : Real.sin x < (43 / 125 : ℝ) := by
    nlinarith
  have hCosLower : (9379 / 10000 : ℝ) < Real.cos x := by
    nlinarith
  have hCosUpper : Real.cos x < (1883 / 2000 : ℝ) := by
    nlinarith
  have hSinPositive : 0 < Real.sin x :=
    lt_trans (by norm_num) hSinLower
  have hCosPositive : 0 < Real.cos x :=
    lt_trans (by norm_num) hCosLower
  have hDoubleAngleLower :
      (100 / 159 : ℝ) ≤ 2 * Real.sin x * Real.cos x := by
    have h₁ :=
      mul_pos (sub_pos.mpr hSinLower) hCosPositive
    have h₂ :=
      mul_pos (by norm_num : (0 : ℝ) < 673 / 2000)
        (sub_pos.mpr hCosLower)
    nlinarith
  have hDoubleAngleUpper :
      2 * Real.sin x * Real.cos x ≤ (100 / 153 : ℝ) := by
    have h₁ :=
      mul_pos (sub_pos.mpr hSinUpper) hCosPositive
    have h₂ :=
      mul_pos (by norm_num : (0 : ℝ) < 43 / 125)
        (sub_pos.mpr hCosUpper)
    nlinarith
  have hDegreeAngle : degreesToRadians 40 = 2 * x := by
    dsimp [degreesToRadians, x]
    ring
  have hSineLower :
      (100 / 159 : ℝ) ≤ Real.sin (degreesToRadians 40) := by
    rw [hDegreeAngle, Real.sin_two_mul]
    exact hDoubleAngleLower
  have hSineUpper :
      Real.sin (degreesToRadians 40) ≤ (100 / 153 : ℝ) := by
    rw [hDegreeAngle, Real.sin_two_mul]
    exact hDoubleAngleUpper
  have hSinePositive : 0 < Real.sin (degreesToRadians 40) :=
    lt_of_lt_of_le (by norm_num) hSineLower
  unfold MatchesDisplayedRatioAnswer
  intro leg
  rw [hExact leg]
  change
    |1 / (6 * Real.sin (degreesToRadians 40)) - 13 / 50| ≤
      (1 / 200 : ℝ)
  have hDenominatorPositive :
      0 < 6 * Real.sin (degreesToRadians 40) :=
    mul_pos (by norm_num) hSinePositive
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hDenominatorPositive]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hDenominatorPositive]
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0758
