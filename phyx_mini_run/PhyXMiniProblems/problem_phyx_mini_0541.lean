import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.QuantumMechanics.FiniteTarget

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0541

/-!
# Sequential Stern--Gerlach probabilities

The question describes a spin-one-half beam whose positive output from a first
Stern--Gerlach analyzer, aligned with the spherical direction `n`, is sent to a
second analyzer aligned with the positive `x` axis.  Angles are dimensionless
radian readouts, and probabilities are dimensionless real readouts.

The supplied raster is not a Stern--Gerlach diagram: it depicts a space station,
a spaceship, a proton, and an asteroid in frames `K` and `K'`.  Its labels and
spatial relations are retained below as a separate source artifact, but they do
not replace the quantum-mechanical setup stated in the question.
-/

/-! ## Spin directions and analyzer outcomes -/

/-- A physical spin/analyzer direction, grounded as the unit metric sphere in
three-dimensional Euclidean space. -/
abbrev SpinDirection :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The two output ports of a spin-one-half Stern--Gerlach analyzer. -/
inductive SpinOutcome where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- The eigenvalue sign associated with an analyzer output. -/
def outcomeSign : SpinOutcome → ℝ
  | .positive => 1
  | .negative => -1

/-- Euclidean scalar product of two physical analyzer directions. -/
def spinDirectionDot (a b : SpinDirection) : ℝ :=
  dotProduct
    (a : EuclideanSpace ℝ (Fin 3))
    (b : EuclideanSpace ℝ (Fin 3))

/-- The unit direction with polar angle `thetaRadians` and azimuthal angle
`phiRadians`, in the usual `(x,y,z)` spherical-coordinate convention. -/
noncomputable def sphericalSpinDirection
    (thetaRadians phiRadians : ℝ) : SpinDirection where
  val := !₂[
    Real.sin thetaRadians * Real.cos phiRadians,
    Real.sin thetaRadians * Real.sin phiRadians,
    Real.cos thetaRadians]
  property := by
    simp [SpinDirection, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq thetaRadians,
      Real.sin_sq_add_cos_sq phiRadians]

/-- The positive Cartesian `x` direction used by the second analyzer. -/
noncomputable def positiveXDirection : SpinDirection where
  val := !₂[(1 : ℝ), 0, 0]
  property := by
    norm_num [SpinDirection, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

/-- Scalar angle readouts printed in the question, expressed in radians. -/
structure AnalyzerAngleReadouts where
  polarThetaRadians : ℝ
  azimuthPhiRadians : ℝ

/-! ## Quantum transition model and governing laws -/

/-- Transition probabilities between analyzer outputs.

The arguments are, in order, the preparation axis, selected preparation
outcome, measurement axis, and measured outcome.  The returned real number is
a dimensionless probability readout. -/
structure SpinHalfTransitionModel where
  transitionProbability :
    SpinDirection → SpinOutcome → SpinDirection → SpinOutcome → ℝ

/-- A sequential two-analyzer experiment.

The selected output of the first analyzer prepares the beam incident on the
second analyzer.  `secondOutcomeProbabilityReadout` is kept distinct from the
abstract transition model until the apparatus-semantics premise relates them.
-/
structure SequentialSternGerlachExperiment where
  transitionModel : SpinHalfTransitionModel
  firstAnalyzerAxis : SpinDirection
  selectedFirstOutput : SpinOutcome
  secondAnalyzerAxis : SpinDirection
  secondOutcomeProbabilityReadout : SpinOutcome → ℝ

/-- General spin-one-half Born transition law for arbitrary preparation and
measurement axes and for both output signs.

This law does not mention the angles or numerical probabilities of the current
question. -/
structure SatisfiesSpinHalfBornRule
    (model : SpinHalfTransitionModel) : Prop where
  probabilityBounds :
    ∀ preparedAxis preparedOutcome measuredAxis measuredOutcome,
      0 ≤ model.transitionProbability
          preparedAxis preparedOutcome measuredAxis measuredOutcome ∧
        model.transitionProbability
          preparedAxis preparedOutcome measuredAxis measuredOutcome ≤ 1
  complementaryOutcomes :
    ∀ preparedAxis preparedOutcome measuredAxis,
      model.transitionProbability
          preparedAxis preparedOutcome measuredAxis .positive +
        model.transitionProbability
          preparedAxis preparedOutcome measuredAxis .negative = 1
  bornTransitionLaw :
    ∀ preparedAxis preparedOutcome measuredAxis measuredOutcome,
      model.transitionProbability
          preparedAxis preparedOutcome measuredAxis measuredOutcome =
        (1 + outcomeSign preparedOutcome * outcomeSign measuredOutcome *
          spinDirectionDot preparedAxis measuredAxis) / 2

/-- The apparatus readout is the transition probability from the selected
first-analyzer branch to the indicated second-analyzer branch. -/
structure SatisfiesSequentialAnalyzerSemantics
    (experiment : SequentialSternGerlachExperiment) : Prop where
  outcomeReadoutIsConditionalTransition :
    ∀ measuredOutcome,
      experiment.secondOutcomeProbabilityReadout measuredOutcome =
        experiment.transitionModel.transitionProbability
          experiment.firstAnalyzerAxis
          experiment.selectedFirstOutput
          experiment.secondAnalyzerAxis
          measuredOutcome

/-- The prose readouts and analyzer arrangement in the quantum question.

The first analyzer selects the positive branch along the specified spherical
axis; the second analyzer measures along positive `x`.  No target probability
appears here. -/
structure MatchesSternGerlachQuestion
    (experiment : SequentialSternGerlachExperiment)
    (angles : AnalyzerAngleReadouts) : Prop where
  thetaReadout : angles.polarThetaRadians = 2 * Real.pi / 3
  phiReadout : angles.azimuthPhiRadians = Real.pi / 4
  firstAnalyzerAlignedWithN :
    experiment.firstAnalyzerAxis =
      sphericalSpinDirection
        angles.polarThetaRadians angles.azimuthPhiRadians
  positiveFirstBranchSelected :
    experiment.selectedFirstOutput = .positive
  secondAnalyzerAlignedWithPositiveX :
    experiment.secondAnalyzerAxis = positiveXDirection

/-! ## The incompatible supplied raster, preserved as source evidence -/

/-- Reference-frame labels visible in the supplied raster. -/
inductive RasterFrame where
  | K
  | KPrime
  deriving DecidableEq, Fintype, Repr

/-- Object labels visible from left to right in the supplied raster. -/
inductive RasterObject where
  | spaceStation
  | spaceship
  | proton
  | asteroid
  deriving DecidableEq, Fintype, Repr

/-- Coordinate-axis labels visible in the supplied raster. -/
inductive RasterAxis where
  | x
  | y
  | xPrime
  | yPrime
  deriving DecidableEq, Fintype, Repr

/-- Velocity symbols visible in the supplied raster. -/
inductive RasterVelocitySymbol where
  | v
  | u
  | uPrime
  deriving DecidableEq, Fintype, Repr

/-- Calibrated readouts from the supplied image artifact.

Horizontal coordinates are dimensionless image-coordinate readouts used only
for ordering.  Velocity arrows are two-dimensional coordinate readouts in an
unspecified common speed unit, since the raster prints no numerical scale.
-/
structure SuppliedRelativityRaster where
  printedFrameLabel : RasterFrame → String
  printedObjectLabel : RasterObject → String
  printedAxisLabel : RasterAxis → String
  velocityArrowReadout : RasterVelocitySymbol → EuclideanSpace ℝ (Fin 2)
  horizontalImageCoordinate : RasterObject → ℝ
  spaceStationShownAtRestInK : Bool
  depictsSternGerlachApparatus : Bool

/-- A two-dimensional arrow points strictly in the positive horizontal
direction. -/
def PointsAlongPositiveHorizontalAxis
    (arrow : EuclideanSpace ℝ (Fin 2)) : Prop :=
  0 < arrow 0 ∧ arrow 1 = 0

/-- Literal labels and spatial relations read from the supplied raster.

The last field explicitly records the source mismatch: the image is a
relativity illustration rather than the analyzer diagram described by the
question. -/
structure MatchesSuppliedRelativityRaster
    (raster : SuppliedRelativityRaster) : Prop where
  frameKText : raster.printedFrameLabel .K = "System K at rest"
  frameKPrimeText : raster.printedFrameLabel .KPrime = "System K'"
  stationText : raster.printedObjectLabel .spaceStation = "Space station"
  spaceshipText : raster.printedObjectLabel .spaceship = "Spaceship"
  protonText : raster.printedObjectLabel .proton = "Proton"
  asteroidText : raster.printedObjectLabel .asteroid = "Asteroid"
  axisXText : raster.printedAxisLabel .x = "x"
  axisYText : raster.printedAxisLabel .y = "y"
  axisXPrimeText : raster.printedAxisLabel .xPrime = "x'"
  axisYPrimeText : raster.printedAxisLabel .yPrime = "y'"
  velocityArrowsPointRight :
    ∀ symbol, PointsAlongPositiveHorizontalAxis
      (raster.velocityArrowReadout symbol)
  objectsShownLeftToRight :
    raster.horizontalImageCoordinate .spaceStation <
      raster.horizontalImageCoordinate .spaceship ∧
    raster.horizontalImageCoordinate .spaceship <
      raster.horizontalImageCoordinate .proton ∧
    raster.horizontalImageCoordinate .proton <
      raster.horizontalImageCoordinate .asteroid
  stationAtRestReadout : raster.spaceStationShownAtRestInK = true
  notASternGerlachRaster : raster.depictsSternGerlachApparatus = false

/-! ## Displayed choices and formal targets -/

/-- Labels of the four answer choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed `(P_{+x}, P_{-x})` pair for each answer choice. -/
def displayedProbabilityPair : AnswerChoice → ℝ × ℝ
  | .A => (688 / 1000, 312 / 1000)
  | .B => (883 / 1000, 117 / 1000)
  | .C => (765 / 1000, 235 / 1000)
  | .D => (806 / 1000, 194 / 1000)

/-- The answer recorded in the dataset, retained only as source metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Absolute-error comparison for dimensionless probability readouts. -/
def ProbabilityApproximatelyEqual
    (tolerance actual displayed : ℝ) : Prop :=
  |actual - displayed| < tolerance

/-- A displayed pair agrees with both modeled branch probabilities to the
chosen absolute tolerance. -/
def MatchesDisplayedChoiceWithin
    (experiment : SequentialSternGerlachExperiment)
    (tolerance : ℝ) (choice : AnswerChoice) : Prop :=
  ProbabilityApproximatelyEqual tolerance
      (experiment.secondOutcomeProbabilityReadout .positive)
      (displayedProbabilityPair choice).1 ∧
    ProbabilityApproximatelyEqual tolerance
      (experiment.secondOutcomeProbabilityReadout .negative)
      (displayedProbabilityPair choice).2

/-- A choice is the unique displayed pair agreeing with the model. -/
def IsUniqueMatchingAnswerChoice
    (experiment : SequentialSternGerlachExperiment)
    (tolerance : ℝ) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedChoiceWithin experiment tolerance choice ∧
    ∀ other,
      MatchesDisplayedChoiceWithin experiment tolerance other →
        other = choice

/-- The stated angles give `n · x = sqrt 6 / 4` in the adopted spherical
coordinate convention. -/
lemma specifiedDirection_dot_positiveX :
    spinDirectionDot
        (sphericalSpinDirection (2 * Real.pi / 3) (Real.pi / 4))
        positiveXDirection =
      Real.sqrt 6 / 4 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
  simp [spinDirectionDot, sphericalSpinDirection, positiveXDirection,
    dotProduct, Fin.sum_univ_succ, Real.sin_pi_sub,
    Real.sin_pi_div_three, Real.cos_pi_div_four]
  ring_nf
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3)]
  norm_num

/-- The second analyzer yields
`P(+x) = (4 + sqrt 6)/8 ≈ 0.806` and
`P(-x) = (4 - sqrt 6)/8 ≈ 0.194`, uniquely selecting choice D at an absolute
tolerance of `0.0005`.

The `raster` premise preserves the unrelated supplied image as source evidence;
it contributes no quantum law and hence cannot determine the answer.

This formalizes blueprint label `thm:physics:phyx_mini_0541:target`.
-/
theorem problem_phyx_mini_0541
    (experiment : SequentialSternGerlachExperiment)
    (angles : AnalyzerAngleReadouts)
    (raster : SuppliedRelativityRaster)
    (hQuestion : MatchesSternGerlachQuestion experiment angles)
    (hSemantics : SatisfiesSequentialAnalyzerSemantics experiment)
    (hBorn : SatisfiesSpinHalfBornRule experiment.transitionModel)
    (hRaster : MatchesSuppliedRelativityRaster raster) :
    experiment.secondOutcomeProbabilityReadout .positive =
        (4 + Real.sqrt 6) / 8 ∧
      experiment.secondOutcomeProbabilityReadout .negative =
        (4 - Real.sqrt 6) / 8 ∧
      ProbabilityApproximatelyEqual (1 / 2000)
        (experiment.secondOutcomeProbabilityReadout .positive) (806 / 1000) ∧
      ProbabilityApproximatelyEqual (1 / 2000)
        (experiment.secondOutcomeProbabilityReadout .negative) (194 / 1000) ∧
      IsUniqueMatchingAnswerChoice experiment (1 / 2000) .D := by
  have hPos :
      experiment.secondOutcomeProbabilityReadout .positive =
        (4 + Real.sqrt 6) / 8 := by
    rw [hSemantics.outcomeReadoutIsConditionalTransition,
      hBorn.bornTransitionLaw, hQuestion.firstAnalyzerAlignedWithN,
      hQuestion.positiveFirstBranchSelected,
      hQuestion.secondAnalyzerAlignedWithPositiveX, hQuestion.thetaReadout,
      hQuestion.phiReadout, specifiedDirection_dot_positiveX]
    norm_num [outcomeSign]
    ring
  have hNeg :
      experiment.secondOutcomeProbabilityReadout .negative =
        (4 - Real.sqrt 6) / 8 := by
    rw [hSemantics.outcomeReadoutIsConditionalTransition,
      hBorn.bornTransitionLaw, hQuestion.firstAnalyzerAlignedWithN,
      hQuestion.positiveFirstBranchSelected,
      hQuestion.secondAnalyzerAlignedWithPositiveX, hQuestion.thetaReadout,
      hQuestion.phiReadout, specifiedDirection_dot_positiveX]
    norm_num [outcomeSign]
    ring
  have hSqrtSq : Real.sqrt 6 ^ 2 = (6 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtNonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hPosApprox :
      ProbabilityApproximatelyEqual (1 / 2000)
        (experiment.secondOutcomeProbabilityReadout .positive)
        (806 / 1000) := by
    rw [hPos, ProbabilityApproximatelyEqual, abs_lt]
    constructor <;> nlinarith [hSqrtSq]
  have hNegApprox :
      ProbabilityApproximatelyEqual (1 / 2000)
        (experiment.secondOutcomeProbabilityReadout .negative)
        (194 / 1000) := by
    rw [hNeg, ProbabilityApproximatelyEqual, abs_lt]
    constructor <;> nlinarith [hSqrtSq]
  have hUnique :
      IsUniqueMatchingAnswerChoice experiment (1 / 2000) .D := by
    constructor
    · exact ⟨hPosApprox, hNegApprox⟩
    · intro other hOther
      cases other with
      | A =>
          exfalso
          have h := hOther.1
          rw [hPos, ProbabilityApproximatelyEqual, abs_lt] at h
          norm_num [displayedProbabilityPair] at h
          nlinarith [hSqrtSq]
      | B =>
          exfalso
          have h := hOther.1
          rw [hPos, ProbabilityApproximatelyEqual, abs_lt] at h
          norm_num [displayedProbabilityPair] at h
          nlinarith [hSqrtSq]
      | C =>
          exfalso
          have h := hOther.1
          rw [hPos, ProbabilityApproximatelyEqual, abs_lt] at h
          norm_num [displayedProbabilityPair] at h
          nlinarith [hSqrtSq]
      | D => rfl
  exact ⟨hPos, hNeg, hPosApprox, hNegApprox, hUnique⟩

end PhyXMiniProblems.ProblemPhyXMini0541
