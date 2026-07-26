import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0902

open Dimension

/-!
# Charge on two symmetrically suspended point masses

The primary image shows two equal point masses hanging from a common support.
Each mass is labelled `3.0 g` and `q`, each thread is labelled `1.0 m`, and
each thread makes an angle of `20°` with the dashed vertical centerline.  The
equal charges repel, so the two masses are in a symmetric static equilibrium.

Mass, length, charge magnitude, acceleration, and force magnitude are
unit-independent Physlib `Dimensionful (WithDim ...)` quantities.  Real
numbers occur only at coherent-SI readout boundaries, in radian-valued
trigonometric functions, and in the printed answer choices.

Assumption/target split:

* governing laws: pendulum geometry, weight `W = m g`, horizontal and vertical
  static force balance, and the point-charge Coulomb force law;
* previous-part results: none;
* figure/data readouts: two point masses at rest, equal charge magnitudes,
  repulsion, a common suspension point, the vertical reference line, `3.0 g`
  mass labels, `1.0 m` thread labels, and `20°` angle labels;
* independent reference data: `g = 9.8 m/s²` and the school-level rounded
  Coulomb constant `k = 9 × 10⁹ N m²/C²`;
* current target conclusion: the common charge rounds to `0.75 μC`, uniquely
  selecting recorded answer C.

No setup or premise field assigns the requested charge value or an answer
label.  In particular, equal charging is represented only by equality of two
independent physical charge magnitudes.
-/

/-! ## Dimensionful physical quantities and named readouts -/

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a nonnegative dimensionful scalar in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Gram readout used by the two mass labels in the image. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Coulomb readout of a physical charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Microcoulomb readout used by all four displayed answers. -/
def chargeInMicrocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * chargeInCoulombs charge

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Convert an angle stated in degrees to the radian argument used by Mathlib. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Suspended bodies and literal primary-figure vocabulary -/

/-- The two charged masses on the left and right of the dashed centerline. -/
inductive SuspendedBody where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Individually named visual features in the supplied raster. -/
inductive FigureFeature where
  | horizontalSupport
  | commonSuspensionPoint
  | verticalDashedReference
  | leftThread
  | rightThread
  | leftSphere
  | rightSphere
  | leftAngleArc
  | rightAngleArc
  deriving DecidableEq, Fintype, Repr

/-- The figure feature corresponding to a body's thread. -/
def threadFeature : SuspendedBody → FigureFeature
  | .left => .leftThread
  | .right => .rightThread

/-- The figure feature corresponding to a charged sphere. -/
def sphereFeature : SuspendedBody → FigureFeature
  | .left => .leftSphere
  | .right => .rightSphere

/-- The figure feature corresponding to a marked angle. -/
def angleArcFeature : SuspendedBody → FigureFeature
  | .left => .leftAngleArc
  | .right => .rightAngleArc

/-!
Literal presentation data transcribed from image `902.png`.  The numerical
labels are connected to independent physical quantities in
`MatchesPrimaryChargedPendulumFigure` below.
-/
structure SymmetricChargedPendulumFigure where
  featureShown : FigureFeature → Bool
  threadsMeetAtCommonPoint : Bool
  dashedReferenceIsVertical : Bool
  bodiesAppearAtEqualHeight : Bool
  massLabelGrams : SuspendedBody → ℝ
  threadLengthLabelMeters : SuspendedBody → ℝ
  angleFromVerticalLabelDegrees : SuspendedBody → ℝ
  chargeSymbol : SuspendedBody → String

/-!
Independent physical quantities of the two-body suspension.  Neither charge
magnitude is defined from a displayed answer.  The single repulsion magnitude
is the common action-reaction magnitude of the horizontal Coulomb interaction.
-/
structure ChargedPendulumSetup where
  figure : SymmetricChargedPendulumFigure
  mass : SuspendedBody → MassQuantity
  threadLength : SuspendedBody → LengthQuantity
  chargeMagnitude : SuspendedBody → ChargeMagnitudeQuantity
  angleFromVerticalRadians : SuspendedBody → ℝ
  centerSeparation : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  weightMagnitude : SuspendedBody → ForceMagnitudeQuantity
  threadTensionMagnitude : SuspendedBody → ForceMagnitudeQuantity
  electrostaticRepulsionMagnitude : ForceMagnitudeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  bodyIsPointCharge : SuspendedBody → Bool
  bodyIsAtRest : SuspendedBody → Bool
  interactionIsRepulsive : Bool

/-! ## Scenario data, figure evidence, and physical nondegeneracy -/

/-!
The qualitative scenario stated in the problem prose.  Equal charging is a
relation between two independent quantities; it supplies no numerical charge.
-/
structure MatchesEquallyChargedPointMassScenario
    (setup : ChargedPendulumSetup) : Prop where
  bothBodiesArePointCharges :
    ∀ body, setup.bodyIsPointCharge body = true
  bothBodiesAreAtRest :
    ∀ body, setup.bodyIsAtRest body = true
  chargesHaveEqualMagnitude :
    setup.chargeMagnitude .left = setup.chargeMagnitude .right
  chargesRepel : setup.interactionIsRepulsive = true

/-!
All numerical and geometric readouts taken from the primary image.  In
particular, the repeated symbol `q` records equal naming, not a value for `q`.
-/
structure MatchesPrimaryChargedPendulumFigure
    (setup : ChargedPendulumSetup) : Prop where
  everyNamedFeatureIsShown :
    ∀ feature, setup.figure.featureShown feature = true
  supportShown : setup.figure.featureShown .horizontalSupport = true
  commonSuspensionPointShown :
    setup.figure.featureShown .commonSuspensionPoint = true
  verticalReferenceShown :
    setup.figure.featureShown .verticalDashedReference = true
  bothThreadsShown :
    ∀ body, setup.figure.featureShown (threadFeature body) = true
  bothSpheresShown :
    ∀ body, setup.figure.featureShown (sphereFeature body) = true
  bothAngleArcsShown :
    ∀ body, setup.figure.featureShown (angleArcFeature body) = true
  threadsSharePivot : setup.figure.threadsMeetAtCommonPoint = true
  referenceLineIsVertical :
    setup.figure.dashedReferenceIsVertical = true
  symmetricBodyHeight : setup.figure.bodiesAppearAtEqualHeight = true
  printedMassLabels :
    ∀ body, setup.figure.massLabelGrams body = 3
  physicalMassesMatchLabels :
    ∀ body,
      massInGrams (setup.mass body) = setup.figure.massLabelGrams body
  printedThreadLengthLabels :
    ∀ body, setup.figure.threadLengthLabelMeters body = 1
  physicalThreadLengthsMatchLabels :
    ∀ body,
      lengthInMeters (setup.threadLength body) =
        setup.figure.threadLengthLabelMeters body
  printedAngleLabels :
    ∀ body, setup.figure.angleFromVerticalLabelDegrees body = 20
  physicalAnglesMatchLabels :
    ∀ body,
      setup.angleFromVerticalRadians body =
        degreesToRadians (setup.figure.angleFromVerticalLabelDegrees body)
  printedChargeSymbols :
    ∀ body, setup.figure.chargeSymbol body = "q"

/-! Rounded independent constants used in the textbook calculation. -/
structure UsesTextbookReferenceConstants
    (setup : ChargedPendulumSetup) : Prop where
  earthGravityCalibration :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 9.8
  schoolCoulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Positivity and nondegeneracy conditions selecting the pictured branch. -/
structure HasPhysicalChargedPendulumParameters
    (setup : ChargedPendulumSetup) : Prop where
  massesPositive :
    ∀ body, 0 < massInKilograms (setup.mass body)
  threadLengthsPositive :
    ∀ body, 0 < lengthInMeters (setup.threadLength body)
  chargeMagnitudesPositive :
    ∀ body, 0 < chargeInCoulombs (setup.chargeMagnitude body)
  centerSeparationPositive :
    0 < lengthInMeters setup.centerSeparation
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  weightsPositive :
    ∀ body, 0 < forceInNewtons (setup.weightMagnitude body)
  tensionsPositive :
    ∀ body, 0 < forceInNewtons (setup.threadTensionMagnitude body)
  repulsionPositive :
    0 < forceInNewtons setup.electrostaticRepulsionMagnitude
  anglesPositive :
    ∀ body, 0 < setup.angleFromVerticalRadians body
  anglesAcute :
    ∀ body, setup.angleFromVerticalRadians body < Real.pi / 2
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing geometry and force laws -/

/-!
For two threads meeting at one pivot on opposite sides of the vertical line,
the center separation is the sum of their horizontal offsets.  Equality of
the vertical drops records the equal-height symmetry visible in the image.
-/
structure SatisfiesSymmetricSuspensionGeometry
    (setup : ChargedPendulumSetup) : Prop where
  centerSeparationFromHorizontalOffsets :
    lengthInMeters setup.centerSeparation =
      lengthInMeters (setup.threadLength .left) *
          Real.sin (setup.angleFromVerticalRadians .left) +
        lengthInMeters (setup.threadLength .right) *
          Real.sin (setup.angleFromVerticalRadians .right)
  equalVerticalDrops :
    lengthInMeters (setup.threadLength .left) *
        Real.cos (setup.angleFromVerticalRadians .left) =
      lengthInMeters (setup.threadLength .right) *
        Real.cos (setup.angleFromVerticalRadians .right)

/-!
The general ideal point-mass pendulum laws used in the calculation:

* weight magnitude is `m g`;
* vertical tension balances weight;
* horizontal tension balances the repulsive electric force; and
* Coulomb's inverse-square law gives that repulsive force.

These laws relate independent observables and contain neither `0.75 μC` nor
an answer-choice label.
-/
structure SatisfiesChargedPendulumEquilibriumLaws
    (setup : ChargedPendulumSetup) : Prop where
  weightLaw : ∀ body,
    forceInNewtons (setup.weightMagnitude body) =
      massInKilograms (setup.mass body) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude
  verticalStaticBalance : ∀ body,
    forceInNewtons (setup.threadTensionMagnitude body) *
        Real.cos (setup.angleFromVerticalRadians body) =
      forceInNewtons (setup.weightMagnitude body)
  horizontalStaticBalance : ∀ body,
    forceInNewtons (setup.threadTensionMagnitude body) *
        Real.sin (setup.angleFromVerticalRadians body) =
      forceInNewtons setup.electrostaticRepulsionMagnitude
  coulombRepulsionLaw :
    forceInNewtons setup.electrostaticRepulsionMagnitude =
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.chargeMagnitude .left) *
          chargeInCoulombs (setup.chargeMagnitude .right) /
        lengthInMeters setup.centerSeparation ^ 2

/-! ## Derived relation and multiple-choice target -/

/-!
Eliminating tension and the electrostatic-force magnitude gives the exact
squared-charge relation before inserting the displayed numerical data.
-/
lemma common_charge_squared_eq_statics_expression
    (setup : ChargedPendulumSetup)
    (_scenario : MatchesEquallyChargedPointMassScenario setup)
    (_physical : HasPhysicalChargedPendulumParameters setup)
    (_laws : SatisfiesChargedPendulumEquilibriumLaws setup) :
    chargeInCoulombs (setup.chargeMagnitude .left) ^ 2 =
      massInKilograms (setup.mass .left) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          Real.tan (setup.angleFromVerticalRadians .left) *
          lengthInMeters setup.centerSeparation ^ 2 /
        setup.electromagneticSystem.coulombConstant := by
  have hcharge :
      chargeInCoulombs (setup.chargeMagnitude .right) =
        chargeInCoulombs (setup.chargeMagnitude .left) :=
    congrArg chargeInCoulombs _scenario.chargesHaveEqualMagnitude.symm
  have hcos :
      0 < Real.cos (setup.angleFromVerticalRadians .left) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hangle := _physical.anglesPositive .left
      have hpi := Real.pi_pos
      nlinarith only [hangle, hpi]
    · exact _physical.anglesAcute .left
  have hforce :
      forceInNewtons setup.electrostaticRepulsionMagnitude =
        massInKilograms (setup.mass .left) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          Real.tan (setup.angleFromVerticalRadians .left) := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    calc
      forceInNewtons setup.electrostaticRepulsionMagnitude *
          Real.cos (setup.angleFromVerticalRadians .left) =
        (forceInNewtons (setup.threadTensionMagnitude .left) *
            Real.sin (setup.angleFromVerticalRadians .left)) *
          Real.cos (setup.angleFromVerticalRadians .left) := by
            rw [_laws.horizontalStaticBalance .left]
      _ =
        (forceInNewtons (setup.threadTensionMagnitude .left) *
            Real.cos (setup.angleFromVerticalRadians .left)) *
          Real.sin (setup.angleFromVerticalRadians .left) := by ring
      _ =
        forceInNewtons (setup.weightMagnitude .left) *
          Real.sin (setup.angleFromVerticalRadians .left) := by
            rw [_laws.verticalStaticBalance .left]
      _ =
        (massInKilograms (setup.mass .left) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude) *
          Real.sin (setup.angleFromVerticalRadians .left) := by
            rw [_laws.weightLaw .left]
  have hcoulomb :
      forceInNewtons setup.electrostaticRepulsionMagnitude *
          lengthInMeters setup.centerSeparation ^ 2 =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.chargeMagnitude .left) ^ 2 := by
    rw [_laws.coulombRepulsionLaw, hcharge]
    field_simp [ne_of_gt _physical.centerSeparationPositive]
  rw [hforce] at hcoulomb
  field_simp [ne_of_gt _physical.coulombConstantPositive]
  nlinarith only [hcoulomb]

/-- Labels of the four charge answers printed in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Charge magnitude in microcoulombs printed beside each answer label. -/
def AnswerChoice.chargeInMicrocoulombs : AnswerChoice → ℝ
  | .A => 7 / 20
  | .B => 11 / 20
  | .C => 3 / 4
  | .D => 7 / 4

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A calculated charge agrees with an answer displayed to the nearest hundredth
of a microcoulomb when it is within half of `0.01 μC` of that displayed value.
The definition is generic and does not privilege answer C.
-/
def MatchesDisplayedChargeAnswer
    (setup : ChargedPendulumSetup) (choice : AnswerChoice) : Prop :=
  ∀ body,
    |chargeInMicrocoulombs (setup.chargeMagnitude body) -
        choice.chargeInMicrocoulombs| ≤ 1 / 200

/-!
**Blueprint target** `thm:physics:phyx_mini_0902:target`.

The symmetric geometry gives a separation `2 sin(20°) m`.  Static balance and
Coulomb's law then give an unrounded common charge of about `0.7459 μC`, which
rounds to `0.75 μC`.  Thus recorded answer C is compatible with both physical
charges and is the unique compatible displayed choice.
-/
theorem problem_phyx_mini_0902
    (setup : ChargedPendulumSetup)
    (_scenario : MatchesEquallyChargedPointMassScenario setup)
    (_figure : MatchesPrimaryChargedPendulumFigure setup)
    (_constants : UsesTextbookReferenceConstants setup)
    (_physical : HasPhysicalChargedPendulumParameters setup)
    (_geometry : SatisfiesSymmetricSuspensionGeometry setup)
    (_laws : SatisfiesChargedPendulumEquilibriumLaws setup) :
    MatchesDisplayedChargeAnswer setup recordedDatasetAnswer ∧
      (∀ choice : AnswerChoice,
        MatchesDisplayedChargeAnswer setup choice →
          choice = recordedDatasetAnswer) := by
  have hmass :
      massInKilograms (setup.mass .left) = 3 / 1000 := by
    have h :=
      (_figure.physicalMassesMatchLabels .left).trans
        (_figure.printedMassLabels .left)
    norm_num [massInGrams] at h ⊢
    linarith only [h]
  have hlength_left :
      lengthInMeters (setup.threadLength .left) = 1 :=
    (_figure.physicalThreadLengthsMatchLabels .left).trans
      (_figure.printedThreadLengthLabels .left)
  have hlength_right :
      lengthInMeters (setup.threadLength .right) = 1 :=
    (_figure.physicalThreadLengthsMatchLabels .right).trans
      (_figure.printedThreadLengthLabels .right)
  have hangle_left :
      setup.angleFromVerticalRadians .left = Real.pi / 9 := by
    calc
      setup.angleFromVerticalRadians .left =
          degreesToRadians
            (setup.figure.angleFromVerticalLabelDegrees .left) :=
        _figure.physicalAnglesMatchLabels .left
      _ = degreesToRadians 20 := by
        rw [_figure.printedAngleLabels .left]
      _ = Real.pi / 9 := by
        norm_num [degreesToRadians]
        ring
  have hangle_right :
      setup.angleFromVerticalRadians .right = Real.pi / 9 := by
    calc
      setup.angleFromVerticalRadians .right =
          degreesToRadians
            (setup.figure.angleFromVerticalLabelDegrees .right) :=
        _figure.physicalAnglesMatchLabels .right
      _ = degreesToRadians 20 := by
        rw [_figure.printedAngleLabels .right]
      _ = Real.pi / 9 := by
        norm_num [degreesToRadians]
        ring
  have hseparation :
      lengthInMeters setup.centerSeparation =
        2 * Real.sin (Real.pi / 9) := by
    rw [_geometry.centerSeparationFromHorizontalOffsets, hlength_left,
      hlength_right, hangle_left, hangle_right]
    ring
  have hcos_pos : 0 < Real.cos (Real.pi / 9) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith only [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (Real.pi / 9) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;>
      nlinarith only [Real.pi_pos]
  have hcos_cubic :
      4 * Real.cos (Real.pi / 9) ^ 3 -
          3 * Real.cos (Real.pi / 9) = 1 / 2 := by
    have htriple :
        Real.cos (3 * (Real.pi / 9)) =
          4 * Real.cos (Real.pi / 9) ^ 3 -
            3 * Real.cos (Real.pi / 9) := by
      rw [show
          3 * (Real.pi / 9) =
            (Real.pi / 9 + Real.pi / 9) + Real.pi / 9 by ring,
        Real.cos_add, Real.cos_add, Real.sin_add]
      have hpythagorean :=
        Real.sin_sq_add_cos_sq (Real.pi / 9)
      linear_combination
        (-3 * Real.cos (Real.pi / 9)) * hpythagorean
    rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring,
      Real.cos_pi_div_three] at htriple
    norm_num at htriple ⊢
    linarith only [htriple]
  have hcos_three_quarters :
      (3 : ℝ) / 4 < Real.cos (Real.pi / 9) := by
    by_contra h
    have hle :
        Real.cos (Real.pi / 9) ≤ (3 : ℝ) / 4 :=
      le_of_not_gt h
    have hcos_sq :
        Real.cos (Real.pi / 9) ^ 2 ≤ ((3 : ℝ) / 4) ^ 2 :=
      (sq_le_sq₀ hcos_pos.le (by norm_num)).mpr hle
    have hfactor_nonpositive :
        4 * Real.cos (Real.pi / 9) ^ 2 - 3 ≤ 0 := by
      linarith only [hcos_sq]
    have hproduct_nonpositive :
        Real.cos (Real.pi / 9) *
            (4 * Real.cos (Real.pi / 9) ^ 2 - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcos_pos.le
        hfactor_nonpositive
    have hfactorization :
        Real.cos (Real.pi / 9) *
            (4 * Real.cos (Real.pi / 9) ^ 2 - 3) = 1 / 2 := by
      calc
        Real.cos (Real.pi / 9) *
              (4 * Real.cos (Real.pi / 9) ^ 2 - 3) =
            4 * Real.cos (Real.pi / 9) ^ 3 -
              3 * Real.cos (Real.pi / 9) := by ring
        _ = 1 / 2 := hcos_cubic
    linarith only [hproduct_nonpositive, hfactorization]
  have hcos_lower :
      (939 : ℝ) / 1000 < Real.cos (Real.pi / 9) := by
    by_contra h
    have hle :
        Real.cos (Real.pi / 9) ≤ (939 : ℝ) / 1000 :=
      le_of_not_gt h
    have hbracket :
        0 <
          4 *
              ((939 / 1000 : ℝ) ^ 2 +
                (939 / 1000) * Real.cos (Real.pi / 9) +
                Real.cos (Real.pi / 9) ^ 2) -
            3 := by
      have hcos_sq :
          ((3 : ℝ) / 4) ^ 2 <
            Real.cos (Real.pi / 9) ^ 2 :=
        (sq_lt_sq₀ (by norm_num) hcos_pos.le).mpr
          hcos_three_quarters
      have hmixed :
          ((3 : ℝ) / 4) ^ 2 <
            (939 / 1000) * Real.cos (Real.pi / 9) := by
        calc
          ((3 : ℝ) / 4) ^ 2 <
              (3 / 4) * Real.cos (Real.pi / 9) :=
            by
              simpa [pow_two] using
                mul_lt_mul_of_pos_left hcos_three_quarters
                  (show (0 : ℝ) < 3 / 4 by norm_num)
          _ < (939 / 1000) * Real.cos (Real.pi / 9) :=
            mul_lt_mul_of_pos_right
              (show (3 : ℝ) / 4 < 939 / 1000 by norm_num) hcos_pos
      have hconstant :
          ((3 : ℝ) / 4) ^ 2 < (939 / 1000) ^ 2 := by
        norm_num
      linarith only [hcos_sq, hmixed, hconstant]
    have hmonotone :
        4 * Real.cos (Real.pi / 9) ^ 3 -
            3 * Real.cos (Real.pi / 9) ≤
          4 * (939 / 1000 : ℝ) ^ 3 - 3 * (939 / 1000) := by
      have hnonnegative :
          0 ≤
            (939 / 1000 - Real.cos (Real.pi / 9)) *
              (4 *
                  ((939 / 1000 : ℝ) ^ 2 +
                    (939 / 1000) * Real.cos (Real.pi / 9) +
                    Real.cos (Real.pi / 9) ^ 2) -
                3) :=
        mul_nonneg (sub_nonneg.mpr hle) hbracket.le
      calc
        4 * Real.cos (Real.pi / 9) ^ 3 -
              3 * Real.cos (Real.pi / 9) =
            (4 * (939 / 1000 : ℝ) ^ 3 - 3 * (939 / 1000)) -
              (939 / 1000 - Real.cos (Real.pi / 9)) *
                (4 *
                    ((939 / 1000 : ℝ) ^ 2 +
                      (939 / 1000) * Real.cos (Real.pi / 9) +
                      Real.cos (Real.pi / 9) ^ 2) -
                  3) := by ring
        _ ≤ 4 * (939 / 1000 : ℝ) ^ 3 - 3 * (939 / 1000) :=
          sub_le_self _ hnonnegative
    have hconstant :
        4 * (939 / 1000 : ℝ) ^ 3 - 3 * (939 / 1000) <
          1 / 2 := by
      norm_num
    linarith only [hcos_cubic, hmonotone, hconstant]
  have hcos_upper :
      Real.cos (Real.pi / 9) < (9397 : ℝ) / 10000 := by
    by_contra h
    have hge :
        (9397 : ℝ) / 10000 ≤ Real.cos (Real.pi / 9) :=
      le_of_not_gt h
    have hbracket :
        0 <
          4 *
              (Real.cos (Real.pi / 9) ^ 2 +
                Real.cos (Real.pi / 9) * (9397 / 10000) +
                (9397 / 10000 : ℝ) ^ 2) -
            3 := by
      have hcos_sq :
          ((3 : ℝ) / 4) ^ 2 <
            Real.cos (Real.pi / 9) ^ 2 :=
        (sq_lt_sq₀ (by norm_num) hcos_pos.le).mpr
          hcos_three_quarters
      have hmixed :
          ((3 : ℝ) / 4) ^ 2 <
            Real.cos (Real.pi / 9) * (9397 / 10000) := by
        calc
          ((3 : ℝ) / 4) ^ 2 <
              Real.cos (Real.pi / 9) * (3 / 4) :=
            by
              simpa [pow_two] using
                mul_lt_mul_of_pos_right hcos_three_quarters
                  (show (0 : ℝ) < 3 / 4 by norm_num)
          _ <
              Real.cos (Real.pi / 9) * (9397 / 10000) :=
            mul_lt_mul_of_pos_left
              (show (3 : ℝ) / 4 < 9397 / 10000 by norm_num) hcos_pos
      have hconstant :
          ((3 : ℝ) / 4) ^ 2 < (9397 / 10000) ^ 2 := by
        norm_num
      linarith only [hcos_sq, hmixed, hconstant]
    have hmonotone :
        4 * (9397 / 10000 : ℝ) ^ 3 - 3 * (9397 / 10000) ≤
          4 * Real.cos (Real.pi / 9) ^ 3 -
            3 * Real.cos (Real.pi / 9) := by
      have hnonnegative :
          0 ≤
            (Real.cos (Real.pi / 9) - 9397 / 10000) *
              (4 *
                  (Real.cos (Real.pi / 9) ^ 2 +
                    Real.cos (Real.pi / 9) * (9397 / 10000) +
                    (9397 / 10000 : ℝ) ^ 2) -
                3) :=
        mul_nonneg (sub_nonneg.mpr hge) hbracket.le
      calc
        4 * (9397 / 10000 : ℝ) ^ 3 - 3 * (9397 / 10000) =
            (4 * Real.cos (Real.pi / 9) ^ 3 -
                3 * Real.cos (Real.pi / 9)) -
              (Real.cos (Real.pi / 9) - 9397 / 10000) *
                (4 *
                    (Real.cos (Real.pi / 9) ^ 2 +
                      Real.cos (Real.pi / 9) * (9397 / 10000) +
                      (9397 / 10000 : ℝ) ^ 2) -
                  3) := by ring
        _ ≤
            4 * Real.cos (Real.pi / 9) ^ 3 -
              3 * Real.cos (Real.pi / 9) :=
          sub_le_self _ hnonnegative
    have hconstant :
        1 / 2 <
          4 * (9397 / 10000 : ℝ) ^ 3 - 3 * (9397 / 10000) := by
      norm_num
    linarith only [hcos_cubic, hmonotone, hconstant]
  have hpythagorean :=
    Real.sin_sq_add_cos_sq (Real.pi / 9)
  have hsin_lower :
      (1709 : ℝ) / 5000 < Real.sin (Real.pi / 9) := by
    by_contra h
    have hle :
        Real.sin (Real.pi / 9) ≤ (1709 : ℝ) / 5000 :=
      le_of_not_gt h
    have hsin_sq :
        Real.sin (Real.pi / 9) ^ 2 ≤ ((1709 : ℝ) / 5000) ^ 2 :=
      (sq_le_sq₀ hsin_pos.le (by norm_num)).mpr hle
    have hcos_sq :
        Real.cos (Real.pi / 9) ^ 2 < ((9397 : ℝ) / 10000) ^ 2 :=
      (sq_lt_sq₀ hcos_pos.le (by norm_num)).mpr hcos_upper
    linarith only [hpythagorean, hsin_sq, hcos_sq]
  have hsin_upper :
      Real.sin (Real.pi / 9) < (43 : ℝ) / 125 := by
    by_contra h
    have hge :
        (43 : ℝ) / 125 ≤ Real.sin (Real.pi / 9) :=
      le_of_not_gt h
    have hsin_sq :
        ((43 : ℝ) / 125) ^ 2 ≤ Real.sin (Real.pi / 9) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hsin_pos.le).mpr hge
    have hcos_sq :
        ((939 : ℝ) / 1000) ^ 2 <
          Real.cos (Real.pi / 9) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hcos_pos.le).mpr hcos_lower
    linarith only [hpythagorean, hsin_sq, hcos_sq]
  have hcharge_coulombs_squared :=
    common_charge_squared_eq_statics_expression
      setup _scenario _physical _laws
  have hcharge_microcoulombs_squared :
      chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 =
        (196 / 15) *
          Real.sin (Real.pi / 9) ^ 3 /
            Real.cos (Real.pi / 9) := by
    calc
      chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 =
          (10 : ℝ) ^ 12 *
            chargeInCoulombs (setup.chargeMagnitude .left) ^ 2 := by
        norm_num [chargeInMicrocoulombs]
        ring
      _ =
          (10 : ℝ) ^ 12 *
            (massInKilograms (setup.mass .left) *
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                Real.tan (setup.angleFromVerticalRadians .left) *
                lengthInMeters setup.centerSeparation ^ 2 /
              setup.electromagneticSystem.coulombConstant) := by
        rw [hcharge_coulombs_squared]
      _ =
          (196 / 15) *
            Real.sin (Real.pi / 9) ^ 3 /
              Real.cos (Real.pi / 9) := by
        rw [hmass, _constants.earthGravityCalibration, hangle_left,
          hseparation, _constants.schoolCoulombConstantCalibration,
          Real.tan_eq_sin_div_cos]
        norm_num
        field_simp [ne_of_gt hcos_pos]
        ring
  have hcharge_microcoulombs_pos :
      0 < chargeInMicrocoulombs (setup.chargeMagnitude .left) := by
    have hcharge_pos := _physical.chargeMagnitudesPositive .left
    norm_num [chargeInMicrocoulombs]
    positivity
  have hcharge_times_cos :
      chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
          Real.cos (Real.pi / 9) =
        (196 / 15) * Real.sin (Real.pi / 9) ^ 3 := by
    field_simp [ne_of_gt hcos_pos] at hcharge_microcoulombs_squared
    linarith only [hcharge_microcoulombs_squared]
  have hsin_cube_lower :
      ((1709 : ℝ) / 5000) ^ 3 <
        Real.sin (Real.pi / 9) ^ 3 := by
    exact (show Odd 3 by decide).pow_lt_pow.mpr hsin_lower
  have hsin_cube_upper :
      Real.sin (Real.pi / 9) ^ 3 <
        ((43 : ℝ) / 125) ^ 3 := by
    exact (show Odd 3 by decide).pow_lt_pow.mpr hsin_upper
  have hcharge_squared_lower :
      ((149 : ℝ) / 200) ^ 2 <
        chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 := by
    have hcharge_square_pos :
        0 < chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 :=
      sq_pos_of_pos hcharge_microcoulombs_pos
    have hcos_product :
        chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            Real.cos (Real.pi / 9) <
          chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            (9397 / 10000) :=
      mul_lt_mul_of_pos_left hcos_upper hcharge_square_pos
    have hsin_product :
        (196 / 15) * ((1709 : ℝ) / 5000) ^ 3 <
          (196 / 15) * Real.sin (Real.pi / 9) ^ 3 :=
      mul_lt_mul_of_pos_left hsin_cube_lower (by norm_num)
    have hnumerical :
        ((149 : ℝ) / 200) ^ 2 * (9397 / 10000) <
          (196 / 15) * ((1709 : ℝ) / 5000) ^ 3 := by
      norm_num
    have hscaled :
        ((149 : ℝ) / 200) ^ 2 * (9397 / 10000) <
          chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            (9397 / 10000) := by
      calc
        ((149 : ℝ) / 200) ^ 2 * (9397 / 10000) <
            (196 / 15) * ((1709 : ℝ) / 5000) ^ 3 :=
          hnumerical
        _ < (196 / 15) * Real.sin (Real.pi / 9) ^ 3 :=
          hsin_product
        _ =
            chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
              Real.cos (Real.pi / 9) :=
          hcharge_times_cos.symm
        _ <
            chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
              (9397 / 10000) :=
          hcos_product
    linarith only [hscaled]
  have hcharge_squared_upper :
      chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 <
        ((151 : ℝ) / 200) ^ 2 := by
    have hcharge_square_pos :
        0 < chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 :=
      sq_pos_of_pos hcharge_microcoulombs_pos
    have hcos_product :
        chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            (939 / 1000) <
          chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            Real.cos (Real.pi / 9) :=
      mul_lt_mul_of_pos_left hcos_lower hcharge_square_pos
    have hsin_product :
        (196 / 15) * Real.sin (Real.pi / 9) ^ 3 <
          (196 / 15) * ((43 : ℝ) / 125) ^ 3 :=
      mul_lt_mul_of_pos_left hsin_cube_upper (by norm_num)
    have hnumerical :
        (196 / 15) * ((43 : ℝ) / 125) ^ 3 <
          ((151 : ℝ) / 200) ^ 2 * (939 / 1000) := by
      norm_num
    have hscaled :
        chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            (939 / 1000) <
          ((151 : ℝ) / 200) ^ 2 * (939 / 1000) := by
      calc
        chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
            (939 / 1000) <
            chargeInMicrocoulombs (setup.chargeMagnitude .left) ^ 2 *
              Real.cos (Real.pi / 9) :=
          hcos_product
        _ = (196 / 15) * Real.sin (Real.pi / 9) ^ 3 :=
          hcharge_times_cos
        _ < (196 / 15) * ((43 : ℝ) / 125) ^ 3 :=
          hsin_product
        _ < ((151 : ℝ) / 200) ^ 2 * (939 / 1000) :=
          hnumerical
    linarith only [hscaled]
  have hcharge_lower :
      (149 : ℝ) / 200 <
        chargeInMicrocoulombs (setup.chargeMagnitude .left) :=
    (sq_lt_sq₀ (by norm_num) hcharge_microcoulombs_pos.le).mp
      hcharge_squared_lower
  have hcharge_upper :
      chargeInMicrocoulombs (setup.chargeMagnitude .left) <
        (151 : ℝ) / 200 :=
    (sq_lt_sq₀ hcharge_microcoulombs_pos.le (by norm_num)).mp
      hcharge_squared_upper
  have hcommon_charge :
      ∀ body,
        chargeInMicrocoulombs (setup.chargeMagnitude body) =
          chargeInMicrocoulombs (setup.chargeMagnitude .left) := by
    intro body
    cases body with
    | left => rfl
    | right =>
        exact
          congrArg chargeInMicrocoulombs
            _scenario.chargesHaveEqualMagnitude.symm
  constructor
  · intro body
    rw [hcommon_charge body]
    change
      |chargeInMicrocoulombs (setup.chargeMagnitude .left) - 3 / 4| ≤
        1 / 200
    rw [abs_le]
    constructor <;> linarith only [hcharge_lower, hcharge_upper]
  · intro choice hchoice
    have hchoice_left := hchoice .left
    change
      |chargeInMicrocoulombs (setup.chargeMagnitude .left) -
          choice.chargeInMicrocoulombs| ≤ 1 / 200 at hchoice_left
    rw [abs_le] at hchoice_left
    rcases hchoice_left with ⟨hchoice_lower, hchoice_upper⟩
    cases choice with
    | A =>
        exfalso
        norm_num [AnswerChoice.chargeInMicrocoulombs] at hchoice_lower hchoice_upper
        linarith only [hchoice_upper, hcharge_lower]
    | B =>
        exfalso
        norm_num [AnswerChoice.chargeInMicrocoulombs] at hchoice_lower hchoice_upper
        linarith only [hchoice_upper, hcharge_lower]
    | C => rfl
    | D =>
        exfalso
        norm_num [AnswerChoice.chargeInMicrocoulombs] at hchoice_lower hchoice_upper
        linarith only [hchoice_lower, hcharge_upper]

end PhyXMiniProblems.ProblemPhyXMini0902
