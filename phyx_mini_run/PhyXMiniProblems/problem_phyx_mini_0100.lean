import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems.ProblemPhyXMini0100

noncomputable section

/-!
# Total internal reflection at a liquid-covered prism face

A ray enters the short leg of a `30°`--`60°`--`90°` prism normally and then
meets the liquid-covered hypotenuse.  Refractive indices are represented by
Physlib's dimension-tagged type at the dimensionless dimension `1`.  Every
angle field below is a scalar readout in radians, measured either from a named
face or from its normal as documented.
-/

/-- The three vertices identified by their angle labels in the figure. -/
inductive PrismVertex where
  | thirtyDegrees
  | sixtyDegrees
  | rightAngle
  deriving DecidableEq, Repr

/-- The three faces of the triangular prism cross-section. -/
inductive PrismFace where
  /-- The leg opposite the `30°` vertex, through which the ray enters. -/
  | shortLeg
  | longLeg
  | hypotenuse
  deriving DecidableEq, Repr

/--
The geometric and optical quantities belonging to the prism experiment.

`internalRayAngleToHypotenuseRadians` is measured from the hypotenuse itself,
whereas `incidenceAtHypotenuseFromNormalRadians` is measured from the normal
to that face.  No value for the requested liquid index is stored here.
-/
structure PrismLiquidSetup where
  vertexAngleRadians : PrismVertex → ℝ
  entryFace : PrismFace
  liquidCoveredFace : PrismFace
  prismRefractiveIndex : WithDim (1 : Dimension) ℝ
  entryIncidenceFromNormalRadians : ℝ
  internalRayAngleToHypotenuseRadians : ℝ
  incidenceAtHypotenuseFromNormalRadians : ℝ

/-- The labeled faces, vertex angles, and normal-entry datum read from the figure. -/
structure MatchesPrismFigure (setup : PrismLiquidSetup) : Prop where
  thirtyDegreeVertex :
    setup.vertexAngleRadians .thirtyDegrees = Real.pi / 6
  sixtyDegreeVertex :
    setup.vertexAngleRadians .sixtyDegrees = Real.pi / 3
  rightAngleVertex :
    setup.vertexAngleRadians .rightAngle = Real.pi / 2
  lightEntersShortLeg : setup.entryFace = .shortLeg
  liquidCoversHypotenuse : setup.liquidCoveredFace = .hypotenuse
  normalIncidenceAtEntry : setup.entryIncidenceFromNormalRadians = 0

/-- The supplied dimensionless refractive-index readout `n_prism = 1.56`. -/
def MatchesPrismIndexReadout (setup : PrismLiquidSetup) : Prop :=
  setup.prismRefractiveIndex = ⟨(39 : ℝ) / 25⟩

/--
The elementary perpendicular-line geometry followed by the internal ray.

Normal entry makes the ray-to-hypotenuse angle complementary to the `60°`
vertex angle.  Incidence from the hypotenuse normal is in turn complementary
to the ray-to-face angle.  These are governing geometric relations, not a
statement of the requested maximum refractive index.
-/
structure SatisfiesPrismRayGeometry (setup : PrismLiquidSetup) : Prop where
  normalEntryDirection :
    setup.internalRayAngleToHypotenuseRadians =
      Real.pi / 2 - setup.vertexAngleRadians .sixtyDegrees
  faceNormalComplement :
    setup.incidenceAtHypotenuseFromNormalRadians =
      Real.pi / 2 - setup.internalRayAngleToHypotenuseRadians

/-- Positivity and principal acute branches for the physical optical data. -/
structure HasPhysicalPrismParameters (setup : PrismLiquidSetup) : Prop where
  prismIndexPositive : 0 < setup.prismRefractiveIndex.val
  rayAngleToHypotenuseAcute :
    setup.internalRayAngleToHypotenuseRadians ∈ Set.Ioo 0 (Real.pi / 2)
  hypotenuseIncidenceAcute :
    setup.incidenceAtHypotenuseFromNormalRadians ∈ Set.Ioo 0 (Real.pi / 2)

/-!
For a candidate liquid index `n_liquid`, the limiting Snell-law condition is

`n_liquid sin(π/2) ≤ n_prism sin(θ_incidence)`.

The endpoint is included because the question asks for the largest permissible
index: equality is the critical, tangential-transmission boundary convention
used by the textbook calculation.  The strict density ordering separately
records that total internal reflection is from the prism toward the less
optically dense liquid.
-/
def PermitsTotalInternalReflection
    (setup : PrismLiquidSetup)
    (liquidRefractiveIndex : WithDim (1 : Dimension) ℝ) : Prop :=
  0 < liquidRefractiveIndex.val ∧
    liquidRefractiveIndex.val < setup.prismRefractiveIndex.val ∧
    liquidRefractiveIndex.val * Real.sin (Real.pi / 2) ≤
      setup.prismRefractiveIndex.val *
        Real.sin setup.incidenceAtHypotenuseFromNormalRadians

/-- All positive liquid-index readouts admitted by the limiting TIR criterion. -/
def admissibleLiquidRefractiveIndices
    (setup : PrismLiquidSetup) : Set (WithDim (1 : Dimension) ℝ) :=
  {nLiquid | PermitsTotalInternalReflection setup nLiquid}

/--
The liquid index obtained by putting the transmitted critical ray tangent to
the interface in Snell's law.  This names a candidate boundary value; it does
not assert that the candidate is admissible or greatest.
-/
def criticalLiquidIndexCandidate
    (setup : PrismLiquidSetup) : WithDim (1 : Dimension) ℝ :=
  ⟨setup.prismRefractiveIndex.val *
        Real.sin setup.incidenceAtHypotenuseFromNormalRadians /
      Real.sin (Real.pi / 2)⟩

/-- The labels printed beside the four multiple-choice values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless liquid-index value printed for each answer choice. -/
def answerChoiceRefractiveIndex : AnswerChoice → ℝ
  | .A => 135 / 100
  | .B => 243 / 100
  | .C => 94 / 100
  | .D => 119 / 100

/-- A displayed choice is uniquely closest to an exact liquid-index value. -/
def IsClosestAnswerChoice
    (actualIndex : WithDim (1 : Dimension) ℝ)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualIndex.val - answerChoiceRefractiveIndex choice| <
      |actualIndex.val - answerChoiceRefractiveIndex other|

/--
Normal entry through the short leg of the depicted prism makes the incidence
angle at the hypotenuse equal to `60°`.
-/
lemma hypotenuse_incidence_is_sixty_degrees
    (setup : PrismLiquidSetup)
    (figure : MatchesPrismFigure setup)
    (geometry : SatisfiesPrismRayGeometry setup) :
    setup.incidenceAtHypotenuseFromNormalRadians = Real.pi / 3 := by
  rw [geometry.faceNormalComplement, geometry.normalEntryDirection,
    figure.sixtyDegreeVertex]
  ring

/--
With `n_prism = 1.56` and `θ_incidence = 60°`, the critical Snell candidate is
`1.56 sin(60°) = 39 √3 / 50`.
-/
lemma critical_liquid_index_exact
    (setup : PrismLiquidSetup)
    (figure : MatchesPrismFigure setup)
    (indexReadout : MatchesPrismIndexReadout setup)
    (geometry : SatisfiesPrismRayGeometry setup) :
    criticalLiquidIndexCandidate setup =
      (⟨39 * Real.sqrt 3 / 50⟩ : WithDim (1 : Dimension) ℝ) := by
  apply WithDim.ext
  simp only [criticalLiquidIndexCandidate]
  rw [hypotenuse_incidence_is_sixty_degrees setup figure geometry,
    Real.sin_pi_div_three, Real.sin_pi_div_two]
  rw [show setup.prismRefractiveIndex.val = (39 : ℝ) / 25 by
    simpa [MatchesPrismIndexReadout] using congrArg WithDim.val indexReadout]
  ring

/--
The largest dimensionless liquid refractive index allowed by the limiting
total-internal-reflection criterion is `39 √3 / 50`, and this exact value is
closest to the displayed value `1.35`, answer A.

This formalizes `thm:physics:phyx_mini_0100:target`.
-/
theorem maximum_liquid_refractive_index
    (setup : PrismLiquidSetup)
    (figure : MatchesPrismFigure setup)
    (indexReadout : MatchesPrismIndexReadout setup)
    (geometry : SatisfiesPrismRayGeometry setup)
    (physical : HasPhysicalPrismParameters setup) :
    IsGreatest (admissibleLiquidRefractiveIndices setup)
        (⟨39 * Real.sqrt 3 / 50⟩ : WithDim (1 : Dimension) ℝ) ∧
      criticalLiquidIndexCandidate setup =
          (⟨39 * Real.sqrt 3 / 50⟩ : WithDim (1 : Dimension) ℝ) ∧
      IsClosestAnswerChoice
        (⟨39 * Real.sqrt 3 / 50⟩ : WithDim (1 : Dimension) ℝ) .A := by
  have hIncidence :
      setup.incidenceAtHypotenuseFromNormalRadians = Real.pi / 3 :=
    hypotenuse_incidence_is_sixty_degrees setup figure geometry
  have hPrismIndex :
      setup.prismRefractiveIndex.val = (39 : ℝ) / 25 := by
    simpa [MatchesPrismIndexReadout] using
      congrArg WithDim.val indexReadout
  have hPhysicalPrismIndexPositive :
      0 < setup.prismRefractiveIndex.val :=
    physical.prismIndexPositive
  have hSqrtNonnegative : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hSqrtSquare : (Real.sqrt 3) ^ 2 = 3 := by
    norm_num
  have hSqrtPositive : 0 < Real.sqrt 3 := by
    positivity
  have hSqrtLower : (45 : ℝ) / 26 < Real.sqrt 3 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 3 < 2 := by
    nlinarith
  have hActualAboveA :
      (135 : ℝ) / 100 < 39 * Real.sqrt 3 / 50 := by
    nlinarith
  have hActualBelowMidpointAB :
      39 * Real.sqrt 3 / 50 < (189 : ℝ) / 100 := by
    nlinarith
  refine ⟨?_, critical_liquid_index_exact setup figure indexReadout geometry, ?_⟩
  · constructor
    · change PermitsTotalInternalReflection setup
        (⟨39 * Real.sqrt 3 / 50⟩ : WithDim (1 : Dimension) ℝ)
      refine ⟨by positivity, ?_, ?_⟩
      · rw [hPrismIndex]
        nlinarith [hPhysicalPrismIndexPositive]
      · rw [Real.sin_pi_div_two, hPrismIndex, hIncidence,
          Real.sin_pi_div_three]
        nlinarith
    · intro liquid hLiquid
      change liquid.val ≤ 39 * Real.sqrt 3 / 50
      have hSnell := hLiquid.2.2
      rw [Real.sin_pi_div_two, hPrismIndex, hIncidence,
        Real.sin_pi_div_three] at hSnell
      nlinarith
  · intro other hOther
    cases other with
    | A => exact (hOther rfl).elim
    | B =>
        simp only [answerChoiceRefractiveIndex]
        rw [abs_of_nonneg (by linarith [hActualAboveA]),
          abs_of_nonpos (by nlinarith [hSqrtUpper])]
        nlinarith
    | C =>
        simp only [answerChoiceRefractiveIndex]
        rw [abs_of_nonneg (by linarith [hActualAboveA]),
          abs_of_nonneg (by linarith [hActualAboveA])]
        norm_num
    | D =>
        simp only [answerChoiceRefractiveIndex]
        rw [abs_of_nonneg (by linarith [hActualAboveA]),
          abs_of_nonneg (by linarith [hActualAboveA])]
        norm_num

end

end PhyXMiniProblems.ProblemPhyXMini0100
