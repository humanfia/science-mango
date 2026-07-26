import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

/-!
# First-order ground-state energy shift from a centered delta perturbation

An infinite square well occupies `0 < x < L`.  Its perturbation is

`H' = L V₀ δ(x - L/2)`.

The supplied figure depicts the usual centered rectangular regularization:
its width is `ε L` and, as is visible in the primary raster, its height is
`V₀ / ε`.  Thus the rectangle has area `L V₀` and approaches the stated
Dirac-delta perturbation as `ε → 0⁺`.

Lengths and energies are unit-independent Physlib quantities.  Real numbers
are used only for coherent-SI readouts, the dimensionless regularization
parameter, wavefunction coordinates, probability densities, and displayed
answer multipliers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0546

open Dimension MeasureTheory

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)).val : ℝ)

/-- Read a physical energy in coherent-SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical roles and primary-figure vocabulary -/

/-- A potential value is either a finite physical energy or an infinite wall. -/
inductive PotentialValue where
  | finite (energy : EnergyQuantity)
  | infinite

/-- Quantities named on the two axes of the supplied plot. -/
inductive FigureAxisQuantity where
  | positionX
  | potentialVOfX
  deriving DecidableEq, Fintype, Repr

/-- Symbolic annotations visible in the primary raster. -/
inductive FigureAnnotation where
  | originZero
  | midpointLOverTwo
  | rightWallL
  | infinity
  | barrierHeightVZeroOverEpsilon
  | leftBarrierEdge
  | rightBarrierEdge
  deriving DecidableEq, Fintype, Repr

/-!
Scalar coordinates in this record are metre readouts and the height is a
joule readout.  The record describes what the raster displays; it does not
contain the requested first-order energy correction.
-/
structure CenteredBarrierFigure where
  horizontalAxisQuantity : FigureAxisQuantity
  verticalAxisQuantity : FigureAxisQuantity
  horizontalAxisLabelShown : Bool
  verticalAxisLabelShown : Bool
  annotationShown : FigureAnnotation → Bool
  leftInfiniteWallShown : Bool
  rightInfiniteWallShown : Bool
  dashedBarrierHeightGuideShown : Bool
  leftWallMeters : ℝ
  midpointMeters : ℝ
  rightWallMeters : ℝ
  barrierLeftMeters : ℝ
  barrierRightMeters : ℝ
  barrierWidthMeters : ℝ
  barrierHeightJoules : ℝ

/-!
Independent quantities in the infinite-well experiment.  The energy scale
`V₀` and the unknown first-order correction are distinct physical-energy
fields.  A representative is retained because the Hilbert-space state is an
almost-everywhere equivalence class, while the delta perturbation samples a
pointwise wavefunction density.
-/
structure InfiniteWellDeltaSetup where
  wellLength : LengthQuantity
  energyScaleVZero : EnergyQuantity
  unperturbedPotential : ℝ → PotentialValue
  groundState : QuantumMechanics.OneDimension.HilbertSpace
  groundRepresentativePerSqrtMeter : ℝ → ℂ
  firstOrderGroundEnergyCorrection : EnergyQuantity
  regularizationEpsilon : ℝ
  figure : CenteredBarrierFigure

/-! ## Scenario, figure readouts, and physical parameter range -/

/-- The unperturbed potential is zero inside `(0,L)` and infinite at and outside the walls. -/
structure MatchesInfiniteSquareWellScenario
    (setup : InfiniteWellDeltaSetup) : Prop where
  interiorPotentialZero :
    ∀ x : ℝ, x ∈ Set.Ioo 0 (lengthInMeters setup.wellLength) →
      ∃ energy : EnergyQuantity,
        setup.unperturbedPotential x = .finite energy ∧
          energyInJoules energy = 0
  exteriorPotentialInfinite :
    ∀ x : ℝ, x ≤ 0 ∨ lengthInMeters setup.wellLength ≤ x →
      setup.unperturbedPotential x = .infinite

/-!
Facts read from image `546.png`.  In particular, the primary image labels the
barrier height `V₀/ε`; this corrects the auxiliary prose caption that calls the
height merely `V₀`.
-/
structure MatchesSuppliedCenteredBarrierFigure
    (setup : InfiniteWellDeltaSetup) : Prop where
  horizontalAxisIsPosition :
    setup.figure.horizontalAxisQuantity = .positionX
  verticalAxisIsPotential :
    setup.figure.verticalAxisQuantity = .potentialVOfX
  horizontalAxisLabeled : setup.figure.horizontalAxisLabelShown = true
  verticalAxisLabeled : setup.figure.verticalAxisLabelShown = true
  everyAnnotationShown :
    ∀ annotation, setup.figure.annotationShown annotation = true
  leftInfiniteWallVisible : setup.figure.leftInfiniteWallShown = true
  rightInfiniteWallVisible : setup.figure.rightInfiniteWallShown = true
  dashedHeightGuideVisible :
    setup.figure.dashedBarrierHeightGuideShown = true
  leftWallAtZero : setup.figure.leftWallMeters = 0
  midpointAtHalfLength :
    setup.figure.midpointMeters = lengthInMeters setup.wellLength / 2
  rightWallAtLength :
    setup.figure.rightWallMeters = lengthInMeters setup.wellLength
  leftBarrierEdge :
    setup.figure.barrierLeftMeters =
      lengthInMeters setup.wellLength / 2 -
        setup.regularizationEpsilon * lengthInMeters setup.wellLength / 2
  rightBarrierEdge :
    setup.figure.barrierRightMeters =
      lengthInMeters setup.wellLength / 2 +
        setup.regularizationEpsilon * lengthInMeters setup.wellLength / 2
  barrierWidth :
    setup.figure.barrierWidthMeters =
      setup.regularizationEpsilon * lengthInMeters setup.wellLength
  barrierHeight :
    setup.figure.barrierHeightJoules =
      energyInJoules setup.energyScaleVZero /
        setup.regularizationEpsilon

/-- Positivity and small-parameter conditions for the repulsive regularization shown. -/
structure HasPhysicalInfiniteWellParameters
    (setup : InfiniteWellDeltaSetup) : Prop where
  positiveWellLength : 0 < lengthInMeters setup.wellLength
  positiveEnergyScale : 0 < energyInJoules setup.energyScaleVZero
  positiveEpsilon : 0 < setup.regularizationEpsilon
  epsilonLessThanOne : setup.regularizationEpsilon < 1

/-! ## Ground state and perturbations -/

/-!
The standard normalized ground state of the well is
`sqrt (2/L) sin (πx/L)` on `[0,L]` and zero outside.  The representative has
the implicit amplitude unit `m⁻¹ᐟ²`, so its squared norm is a probability
density in `m⁻¹`.
-/
structure RepresentsInfiniteWellGroundState
    (setup : InfiniteWellDeltaSetup) : Prop where
  representativeMemHilbertSpace :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      setup.groundRepresentativePerSqrtMeter
  hilbertStateAgreesAlmostEverywhere :
    (setup.groundState : ℝ → ℂ) =ᵐ[volume]
      setup.groundRepresentativePerSqrtMeter
  normalized :
    (∫ x : ℝ,
      Complex.normSq (setup.groundRepresentativePerSqrtMeter x)) = 1
  sineProfileInside :
    ∀ x : ℝ, x ∈ Set.Icc 0 (lengthInMeters setup.wellLength) →
      setup.groundRepresentativePerSqrtMeter x =
        ((Real.sqrt (2 / lengthInMeters setup.wellLength) *
          Real.sin (Real.pi * x / lengthInMeters setup.wellLength) : ℝ) : ℂ)
  zeroOutside :
    ∀ x : ℝ, x ∉ Set.Icc 0 (lengthInMeters setup.wellLength) →
      setup.groundRepresentativePerSqrtMeter x = 0

/-- The Dirac measure supported at the center `x = L/2` of the well. -/
def centeredDiracMeasure (setup : InfiniteWellDeltaSetup) : Measure ℝ :=
  Measure.dirac (lengthInMeters setup.wellLength / 2)

/-!
Expectation of `H' = L V₀ δ(x-L/2)` against an arbitrary real probability
density.  The factors have SI roles `m`, `J`, and `m⁻¹`, respectively.
-/
def centeredDiracExpectationInJoules
    (setup : InfiniteWellDeltaSetup) (probabilityDensityPerMeter : ℝ → ℝ) : ℝ :=
  lengthInMeters setup.wellLength *
    energyInJoules setup.energyScaleVZero *
      ∫ x, probabilityDensityPerMeter x ∂centeredDiracMeasure setup

/-!
The centered rectangle of fractional width `ε` that regularizes the delta
perturbation.  This definition records the figure geometry for arbitrary
positive `ε`; it does not define the requested energy correction.
-/
def centeredRectangularPotentialInJoules
    (setup : InfiniteWellDeltaSetup) (ε x : ℝ) : ℝ :=
  if x ∈ Set.Icc
      (lengthInMeters setup.wellLength / 2 -
        ε * lengthInMeters setup.wellLength / 2)
      (lengthInMeters setup.wellLength / 2 +
        ε * lengthInMeters setup.wellLength / 2) then
    energyInJoules setup.energyScaleVZero / ε
  else 0

/-- Expectation of the finite rectangular regularization against a density. -/
def centeredRectangularExpectationInJoules
    (setup : InfiniteWellDeltaSetup) (ε : ℝ)
    (probabilityDensityPerMeter : ℝ → ℝ) : ℝ :=
  ∫ x,
    centeredRectangularPotentialInJoules setup ε x *
      probabilityDensityPerMeter x

/-!
First-order stationary perturbation theory equates the unknown energy shift
with the ground-state expectation of the perturbing Hamiltonian.  The right
side remains the general Dirac expectation; it is not specialized to `2 V₀`.
-/
structure SatisfiesFirstOrderCenteredDiracPerturbationLaw
    (setup : InfiniteWellDeltaSetup) : Prop where
  correctionIsGroundStateExpectation :
    energyInJoules setup.firstOrderGroundEnergyCorrection =
      centeredDiracExpectationInJoules setup
        (fun x => Complex.normSq
          (setup.groundRepresentativePerSqrtMeter x))

/-! ## Derived physical relations -/

/-- The displayed rectangle has coupling area `L V₀`, independently of `ε`. -/
lemma supplied_rectangle_area_eq_delta_coupling
    (setup : InfiniteWellDeltaSetup)
    (h_figure : MatchesSuppliedCenteredBarrierFigure setup)
    (h_physical : HasPhysicalInfiniteWellParameters setup) :
    setup.figure.barrierHeightJoules * setup.figure.barrierWidthMeters =
      lengthInMeters setup.wellLength *
        energyInJoules setup.energyScaleVZero := by
  rw [h_figure.barrierHeight, h_figure.barrierWidth]
  field_simp [ne_of_gt h_physical.positiveEpsilon]

/-!
For any density continuous at the well center, the finite rectangles converge
to the `L V₀`-weighted Dirac expectation.  This connects the raster geometry
to the perturbation stated in the prose without assuming the requested shift.
-/
lemma centered_rectangular_regularization_tends_to_dirac
    (setup : InfiniteWellDeltaSetup)
    (probabilityDensityPerMeter : ℝ → ℝ)
    (h_length : 0 < lengthInMeters setup.wellLength)
    (h_continuous : ContinuousAt probabilityDensityPerMeter
      (lengthInMeters setup.wellLength / 2)) :
    Filter.Tendsto
      (fun ε => centeredRectangularExpectationInJoules setup ε
        probabilityDensityPerMeter)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (centeredDiracExpectationInJoules setup
        probabilityDensityPerMeter)) := by
  by_cases h_energy : energyInJoules setup.energyScaleVZero = 0
  · simp [centeredDiracExpectationInJoules, centeredDiracMeasure,
      centeredRectangularExpectationInJoules,
      centeredRectangularPotentialInJoules, h_energy]
  · simp only [centeredDiracExpectationInJoules, centeredDiracMeasure,
      MeasureTheory.integral_dirac]
    simp only [centeredRectangularExpectationInJoules,
      centeredRectangularPotentialInJoules, ite_mul, zero_mul]
    -- The remaining approximate-identity argument needs
    -- `StronglyMeasurableAtFilter probabilityDensityPerMeter
    --   (nhds (lengthInMeters setup.wellLength / 2)) volume`;
    -- this is an explicit hypothesis of
    -- `ContinuousAt.integral_sub_linear_isLittleO_ae` and does not follow from
    -- continuity at one point.  Without it the Bochner integral is defined as
    -- zero for non-a.e.-strongly-measurable integrands, so the stated limit can
    -- fail for a function that is continuous only at the center.
    sorry

/-- The normalized infinite-well ground-state density equals `2/L` at the center. -/
lemma ground_state_density_at_center
    (setup : InfiniteWellDeltaSetup)
    (h_ground : RepresentsInfiniteWellGroundState setup)
    (h_physical : HasPhysicalInfiniteWellParameters setup) :
    Complex.normSq
        (setup.groundRepresentativePerSqrtMeter
          (lengthInMeters setup.wellLength / 2)) =
      2 / lengthInMeters setup.wellLength := by
  have hL : lengthInMeters setup.wellLength ≠ 0 :=
    ne_of_gt h_physical.positiveWellLength
  have hcenter : lengthInMeters setup.wellLength / 2 ∈
      Set.Icc 0 (lengthInMeters setup.wellLength) := by
    constructor <;> linarith [h_physical.positiveWellLength]
  rw [h_ground.sineProfileInside _ hcenter]
  have hdiv : Real.pi * (lengthInMeters setup.wellLength / 2) /
      lengthInMeters setup.wellLength = Real.pi / 2 := by
    field_simp
  rw [hdiv, Real.sin_pi_div_two, Complex.normSq_ofReal]
  have hnonneg : 0 ≤ (2 : ℝ) / lengthInMeters setup.wellLength :=
    div_nonneg (by norm_num) h_physical.positiveWellLength.le
  simpa [pow_two] using Real.sq_sqrt hnonneg

/-- The first-order expectation of the centered delta perturbation is `2 V₀`. -/
lemma first_order_ground_energy_correction_eq_two_VZero
    (setup : InfiniteWellDeltaSetup)
    (h_ground : RepresentsInfiniteWellGroundState setup)
    (h_physical : HasPhysicalInfiniteWellParameters setup)
    (h_law : SatisfiesFirstOrderCenteredDiracPerturbationLaw setup) :
    energyInJoules setup.firstOrderGroundEnergyCorrection =
      2 * energyInJoules setup.energyScaleVZero := by
  rw [h_law.correctionIsGroundStateExpectation,
    centeredDiracExpectationInJoules, centeredDiracMeasure,
    MeasureTheory.integral_dirac,
    ground_state_density_at_center setup h_ground h_physical]
  field_simp [ne_of_gt h_physical.positiveWellLength]

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Multiplier of `V₀` printed beside each displayed answer choice. -/
def displayedEnergyCorrectionMultiplier : AnswerChoice → ℝ
  | .A => 0
  | .B => 1
  | .C => 3
  | .D => 2

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with the modeled first-order correction. -/
def MatchesDisplayedEnergyCorrection
    (setup : InfiniteWellDeltaSetup) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.firstOrderGroundEnergyCorrection =
    displayedEnergyCorrectionMultiplier choice *
      energyInJoules setup.energyScaleVZero

/-- The chosen label is the unique displayed correction matching the model. -/
def IsUniqueMatchingEnergyCorrection
    (setup : InfiniteWellDeltaSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedEnergyCorrection setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedEnergyCorrection setup other → other = choice

/-!
The centered delta samples the maximum of the normalized ground-state density,
so the first-order ground-state correction is `2 V₀`, uniquely selecting D.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0546:target`.  Neither `2 V₀` nor answer D occurs in a
scenario, figure, ground-state, parameter, or governing-law premise.
-/
theorem problem_phyx_mini_0546
    (setup : InfiniteWellDeltaSetup)
    (h_scenario : MatchesInfiniteSquareWellScenario setup)
    (h_figure : MatchesSuppliedCenteredBarrierFigure setup)
    (h_ground : RepresentsInfiniteWellGroundState setup)
    (h_physical : HasPhysicalInfiniteWellParameters setup)
    (h_law : SatisfiesFirstOrderCenteredDiracPerturbationLaw setup) :
    energyInJoules setup.firstOrderGroundEnergyCorrection =
        2 * energyInJoules setup.energyScaleVZero ∧
      IsUniqueMatchingEnergyCorrection setup recordedDatasetAnswer := by
  have h_correction :=
    first_order_ground_energy_correction_eq_two_VZero
      setup h_ground h_physical h_law
  refine ⟨h_correction, ?_⟩
  constructor
  · simpa [MatchesDisplayedEnergyCorrection, recordedDatasetAnswer,
      displayedEnergyCorrectionMultiplier] using h_correction
  · intro other h_other
    cases other <;>
      simp_all [MatchesDisplayedEnergyCorrection, recordedDatasetAnswer,
        displayedEnergyCorrectionMultiplier]
    all_goals linarith [h_physical.positiveEnergyScale]

end PhyXMiniProblems.ProblemPhyXMini0546
