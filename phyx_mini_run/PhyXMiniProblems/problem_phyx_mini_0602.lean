import Mathlib
import Physlib.Mathematics.Distribution.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0602

open Dimension
open scoped Matrix

/-!
# Transfer matrix for an attractive double-delta potential

The stationary one-dimensional scattering problem has two attractive point
interactions at `x = -a` and `x = a`.  The complex plane-wave amplitudes on
the far left are `(A, B)`, while those on the far right are `(F, G)`, with

`(F, G)ᵀ = M (A, B)ᵀ`.

Dimensionful quantities are represented with Physlib's `Dimensionful` and
`WithDim`.  Real scalars below are explicitly coherent-SI readouts, metre
coordinates, dimensionless ratios, or probabilities.  The singular potential
itself is a Physlib distribution rather than a scalar-valued placeholder.

Assumption/target split:

* `MatchesDoubleDeltaScenario` records the given potential, its locations,
  and the three free regions;
* `MatchesSuppliedDoubleDeltaFigure` records only facts visible in image 602;
* `HasPhysicalDoubleDeltaParameters` and
  `UsesStandardReducedPlanckConstant` record parameter conditions and unit
  calibration;
* `SatisfiesFreeParticleDispersionLaw` and
  `SatisfiesDoubleDeltaScatteringLaws` state the governing dispersion,
  matching, propagation, and probability laws; and
* the local matrices, total matrix, and physically supported transmission
  formula occur only in lemma/theorem conclusions.

All four answer expressions and the recorded label C are retained only as
dataset metadata.  They are deliberately not asserted by the physics theorem:
the printed C expression has no square on its final trigonometric factor and
uses `mα/(ℏk)` where the matching law gives the dimensionless
`mα/(ℏ²k)`.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent particle mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, `mass * length² / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent action such as reduced Planck's constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative wave number, with physical dimension `length⁻¹`. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/--
The delta-coupling dimension `energy * length = mass * length³ / time²`.
For `V(x) = -α δ(x-x₀)`, `α` has this dimension because `δ` has inverse
length dimension.
-/
def deltaStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative strength `α` of an attractive delta interaction. -/
abbrev DeltaStrengthQuantity : Type :=
  Dimensionful (WithDim deltaStrengthDimension NNReal)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Joule-second readout of an action. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Inverse-metre readout of a wave number. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- Joule-metre readout of the double-delta coupling `α`. -/
def deltaStrengthInJouleMeters (strength : DeltaStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-! ## Matrix, amplitude, potential, and figure vocabulary -/

/-- A column of right- and left-moving dimensionless wave amplitudes. -/
abbrev AmplitudePair : Type := Fin 2 → ℂ

/-- A complex `2 × 2` transfer matrix acting on an amplitude pair. -/
abbrev TransferMatrix : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- A real scalar distribution in the metre coordinate. -/
abbrev RealPotentialDistribution : Type :=
  Physlib.Distribution ℝ ℝ ℝ

/-- The two point interactions, named by the `M₁` and `M₂` labels in the image. -/
inductive PointInteraction where
  | firstM1
  | secondM2
  deriving DecidableEq, Fintype, Repr

/-- The three free-particle regions separated by the two point interactions. -/
inductive FreeRegion where
  | left
  | middle
  | right
  deriving DecidableEq, Fintype, Repr

/-!
Raster-visible data from image 602.  The image labels two separated packets
`M₁`, `M₂`, places `V = 0` under all three intervening regions, and labels the
horizontal axis `x`; it does not visibly print `±a`.
-/
structure SuppliedDoubleDeltaFigure where
  horizontalAxisText : String
  interactionText : PointInteraction → String
  freeRegionText : FreeRegion → String
  showsFirstInteractionLeftOfSecond : Bool
  showsWavePacketAt : PointInteraction → Bool
  showsFreeBracketAt : FreeRegion → Bool

/-!
Independent physical quantities, amplitudes, and transfer data.  The maps
`propagateAcrossM1` and `propagateAcrossM2` act on arbitrary amplitude pairs,
which makes each transfer matrix identifiable rather than constraining it on
only the single displayed scattering state.
-/
structure DoubleDeltaScatteringSetup where
  halfSeparation : LengthQuantity
  particleMass : MassQuantity
  deltaStrength : DeltaStrengthQuantity
  reducedPlanckAction : ActionQuantity
  incidentEnergy : DimEnergy
  waveNumber : WaveNumberQuantity
  potentialEnergyDistributionSI : RealPotentialDistribution
  freePotentialEnergyJoules : FreeRegion → ℝ
  interactionPositionMeters : PointInteraction → ℝ
  leftAmplitudes : AmplitudePair
  middleAmplitudes : AmplitudePair
  rightAmplitudes : AmplitudePair
  propagateAcrossM1 : AmplitudePair → AmplitudePair
  propagateAcrossM2 : AmplitudePair → AmplitudePair
  firstInteractionMatrix : TransferMatrix
  secondInteractionMatrix : TransferMatrix
  totalTransferMatrix : TransferMatrix
  transmissionCoefficient : ℝ
  figure : SuppliedDoubleDeltaFigure

/-- The half-separation `a`, read in metres. -/
def halfSeparationMeters (setup : DoubleDeltaScatteringSetup) : ℝ :=
  lengthInMeters setup.halfSeparation

/-- The particle mass `m`, read in kilograms. -/
def particleMassKilograms (setup : DoubleDeltaScatteringSetup) : ℝ :=
  massInKilograms setup.particleMass

/-- The attractive coupling `α`, read in joule-metres. -/
def deltaStrengthSI (setup : DoubleDeltaScatteringSetup) : ℝ :=
  deltaStrengthInJouleMeters setup.deltaStrength

/-- The reduced Planck action `ℏ`, read in joule-seconds. -/
def reducedPlanckSI (setup : DoubleDeltaScatteringSetup) : ℝ :=
  actionInJouleSeconds setup.reducedPlanckAction

/-- The incident energy `E`, read in joules. -/
def incidentEnergyJoules (setup : DoubleDeltaScatteringSetup) : ℝ :=
  energyInJoules setup.incidentEnergy

/-- The wave number `k`, read in inverse metres. -/
def waveNumberSI (setup : DoubleDeltaScatteringSetup) : ℝ :=
  waveNumberInInverseMeters setup.waveNumber

/-- Source amplitude `A`, incident from the left. -/
def amplitudeA (setup : DoubleDeltaScatteringSetup) : ℂ :=
  setup.leftAmplitudes 0

/-- Source amplitude `B`, outgoing to the left. -/
def amplitudeB (setup : DoubleDeltaScatteringSetup) : ℂ :=
  setup.leftAmplitudes 1

/-- Source amplitude `F`, outgoing to the right. -/
def amplitudeF (setup : DoubleDeltaScatteringSetup) : ℂ :=
  setup.rightAmplitudes 0

/-- Source amplitude `G`, incoming from the right. -/
def amplitudeG (setup : DoubleDeltaScatteringSetup) : ℂ :=
  setup.rightAmplitudes 1

/-! ## Source scenario, figure readouts, and parameter conditions -/

/-!
The potential stated in the prose, including both locations and every
zero-potential region.  The distribution is a coherent-SI representation of
`-α[δ(x+a)+δ(x-a)]`; no pointwise value is assigned at a delta singularity.
-/
structure MatchesDoubleDeltaScenario
    (setup : DoubleDeltaScatteringSetup) : Prop where
  firstInteractionAtMinusA :
    setup.interactionPositionMeters .firstM1 =
      -halfSeparationMeters setup
  secondInteractionAtPlusA :
    setup.interactionPositionMeters .secondM2 =
      halfSeparationMeters setup
  doubleAttractiveDeltaPotential :
    setup.potentialEnergyDistributionSI =
      (-deltaStrengthSI setup) •
        (Physlib.Distribution.diracDelta ℝ (-halfSeparationMeters setup) +
          Physlib.Distribution.diracDelta ℝ (halfSeparationMeters setup))
  freePotentialIsZero :
    ∀ region, setup.freePotentialEnergyJoules region = 0

/-- All labels and qualitative features visible in the supplied raster. -/
structure MatchesSuppliedDoubleDeltaFigure
    (setup : DoubleDeltaScatteringSetup) : Prop where
  horizontalAxisLabel : setup.figure.horizontalAxisText = "x"
  firstInteractionLabel :
    setup.figure.interactionText .firstM1 = "M₁"
  secondInteractionLabel :
    setup.figure.interactionText .secondM2 = "M₂"
  allFreeRegionLabels :
    ∀ region, setup.figure.freeRegionText region = "V = 0"
  firstIsDrawnLeftOfSecond :
    setup.figure.showsFirstInteractionLeftOfSecond = true
  bothWavePacketsShown :
    ∀ interaction, setup.figure.showsWavePacketAt interaction = true
  allFreeRegionBracketsShown :
    ∀ region, setup.figure.showsFreeBracketAt region = true

/-- Incidence is from the left: `A ≠ 0` and there is no incoming right wave `G`. -/
structure MatchesLeftIncidentScatteringState
    (setup : DoubleDeltaScatteringSetup) : Prop where
  incidentAmplitudeNonzero : amplitudeA setup ≠ 0
  noIncomingWaveFromRight : amplitudeG setup = 0

/-! Positivity and probability-range conditions on the physical parameters. -/
structure HasPhysicalDoubleDeltaParameters
    (setup : DoubleDeltaScatteringSetup) : Prop where
  halfSeparationPositive : 0 < halfSeparationMeters setup
  particleMassPositive : 0 < particleMassKilograms setup
  deltaStrengthPositive : 0 < deltaStrengthSI setup
  reducedPlanckActionPositive : 0 < reducedPlanckSI setup
  incidentEnergyPositive : 0 < incidentEnergyJoules setup
  waveNumberPositive : 0 < waveNumberSI setup
  transmissionNonnegative : 0 ≤ setup.transmissionCoefficient
  transmissionAtMostOne : setup.transmissionCoefficient ≤ 1

/-!
Physlib's `Constants.ℏ` is the standard reduced Planck constant, expressed in
joule-seconds.  This calibration does not constrain a requested matrix entry
or transmission formula.
-/
structure UsesStandardReducedPlanckConstant
    (setup : DoubleDeltaScatteringSetup) : Prop where
  reducedPlanckActionSI : reducedPlanckSI setup = (Constants.ℏ : ℝ)

/-! ## Governing wave and transfer laws -/

/-- The value of a two-component plane-wave expansion at a metre coordinate. -/
def planeWaveValueAt
    (waveNumber positionMeters : ℝ) (amplitudes : AmplitudePair) : ℂ :=
  amplitudes 0 *
      Complex.exp
        (Complex.I * Complex.ofReal (waveNumber * positionMeters)) +
    amplitudes 1 *
      Complex.exp
        (-Complex.I * Complex.ofReal (waveNumber * positionMeters))

/-- The spatial derivative of the same plane-wave expansion. -/
def planeWaveDerivativeAt
    (waveNumber positionMeters : ℝ) (amplitudes : AmplitudePair) : ℂ :=
  Complex.I * Complex.ofReal waveNumber *
    (amplitudes 0 *
        Complex.exp
          (Complex.I * Complex.ofReal (waveNumber * positionMeters)) -
      amplitudes 1 *
        Complex.exp
          (-Complex.I * Complex.ofReal (waveNumber * positionMeters)))

/-!
Continuity and the derivative jump at one attractive point interaction.
For `V = -α δ(x-x₀)`, the jump is
`ψ'(x₀⁺)-ψ'(x₀⁻) = -(2mα/ℏ²) ψ(x₀)`.
This general boundary law contains no candidate transfer-matrix formula.
-/
structure SatisfiesAttractiveDeltaMatching
    (setup : DoubleDeltaScatteringSetup)
    (positionMeters : ℝ)
    (before after : AmplitudePair) : Prop where
  waveFunctionContinuous :
    planeWaveValueAt (waveNumberSI setup) positionMeters after =
      planeWaveValueAt (waveNumberSI setup) positionMeters before
  derivativeJump :
    planeWaveDerivativeAt (waveNumberSI setup) positionMeters after -
        planeWaveDerivativeAt (waveNumberSI setup) positionMeters before =
      Complex.ofReal
          (-(2 * particleMassKilograms setup * deltaStrengthSI setup) /
            reducedPlanckSI setup ^ 2) *
        planeWaveValueAt (waveNumberSI setup) positionMeters before

/-! The nonrelativistic free-particle dispersion relation `ℏ²k² = 2mE`. -/
structure SatisfiesFreeParticleDispersionLaw
    (setup : DoubleDeltaScatteringSetup) : Prop where
  energyWaveNumberRelation :
    reducedPlanckSI setup ^ 2 * waveNumberSI setup ^ 2 =
      2 * particleMassKilograms setup * incidentEnergyJoules setup

/-!
The two matching operations act on arbitrary amplitudes, their matrices
implement those operations, and the total matrix implements their sequential
action.  The final two fields specialize this generic propagation to the
named amplitudes and define transmission as transmitted-to-incident flux for
equal asymptotic wave numbers.  No matrix entry or closed transmission answer
is assumed here.
-/
structure SatisfiesDoubleDeltaScatteringLaws
    (setup : DoubleDeltaScatteringSetup) : Prop where
  matchingAtFirstInteraction :
    ∀ amplitudes,
      SatisfiesAttractiveDeltaMatching setup
        (setup.interactionPositionMeters .firstM1)
        amplitudes (setup.propagateAcrossM1 amplitudes)
  matchingAtSecondInteraction :
    ∀ amplitudes,
      SatisfiesAttractiveDeltaMatching setup
        (setup.interactionPositionMeters .secondM2)
        amplitudes (setup.propagateAcrossM2 amplitudes)
  firstMatrixActs :
    ∀ amplitudes,
      setup.propagateAcrossM1 amplitudes =
        setup.firstInteractionMatrix *ᵥ amplitudes
  secondMatrixActs :
    ∀ amplitudes,
      setup.propagateAcrossM2 amplitudes =
        setup.secondInteractionMatrix *ᵥ amplitudes
  totalMatrixActs :
    ∀ amplitudes,
      setup.propagateAcrossM2 (setup.propagateAcrossM1 amplitudes) =
        setup.totalTransferMatrix *ᵥ amplitudes
  namedMiddleAmplitudes :
    setup.middleAmplitudes =
      setup.propagateAcrossM1 setup.leftAmplitudes
  namedRightAmplitudes :
    setup.rightAmplitudes =
      setup.propagateAcrossM2 setup.middleAmplitudes
  transmissionIsAmplitudeNormRatio :
    setup.transmissionCoefficient =
      Complex.normSq (amplitudeF setup / amplitudeA setup)

/-! ## Candidate matrices and displayed answer choices -/

/-- The dimensionless attractive-delta coupling `η = mα/(ℏ²k)`. -/
def dimensionlessDeltaCoupling
    (setup : DoubleDeltaScatteringSetup) : ℝ :=
  particleMassKilograms setup * deltaStrengthSI setup /
    (reducedPlanckSI setup ^ 2 * waveNumberSI setup)

/-!
Candidate transfer matrix for one attractive delta at `positionMeters`.
This is an answer expression, not a field of any premise structure.
-/
def attractiveDeltaTransferMatrix
    (setup : DoubleDeltaScatteringSetup)
    (positionMeters : ℝ) : TransferMatrix :=
  let η : ℂ := Complex.ofReal (dimensionlessDeltaCoupling setup)
  let phaseArgument : ℂ :=
    Complex.ofReal (2 * waveNumberSI setup * positionMeters)
  !![1 + Complex.I * η,
      Complex.I * η * Complex.exp (-Complex.I * phaseArgument);
    -Complex.I * η * Complex.exp (Complex.I * phaseArgument),
      1 - Complex.I * η]

/-!
The explicit total transfer matrix obtained in the source convention
`(F,G)ᵀ = M(A,B)ᵀ`.  Lean indices `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)` correspond
to the source's `M₁₁`, `M₁₂`, `M₂₁`, `M₂₂`.
-/
def explicitDoubleDeltaTransferMatrix
    (setup : DoubleDeltaScatteringSetup) : TransferMatrix :=
  let ηr : ℝ := dimensionlessDeltaCoupling setup
  let η : ℂ := Complex.ofReal ηr
  let ka : ℝ := waveNumberSI setup * halfSeparationMeters setup
  let realOffDiagonal : ℂ :=
    Complex.ofReal (Real.cos (2 * ka) - ηr * Real.sin (2 * ka))
  !![(1 + Complex.I * η) ^ 2 +
        η ^ 2 * Complex.exp (-4 * Complex.I * Complex.ofReal ka),
      2 * Complex.I * η * realOffDiagonal;
    -2 * Complex.I * η * realOffDiagonal,
      (1 - Complex.I * η) ^ 2 +
        η ^ 2 * Complex.exp (4 * Complex.I * Complex.ofReal ka)]

/-- Labels of the four expressions printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The literal coefficient printed beside each answer label.  These are scalar
readout formulas; no option is used as a premise.
-/
def displayedTransmissionCoefficient
    (setup : DoubleDeltaScatteringSetup) (choice : AnswerChoice) : ℝ :=
  let m := particleMassKilograms setup
  let α := deltaStrengthSI setup
  let ℏ := reducedPlanckSI setup
  let E := incidentEnergyJoules setup
  let k := waveNumberSI setup
  let a := halfSeparationMeters setup
  match choice with
  | .A =>
      (1 + m * α ^ 2 / (ℏ ^ 2 * E) *
        (Real.sin (2 * k * a) + ℏ * k / (m * α)) ^ 2)⁻¹
  | .B =>
      (1 + (2 * α / k) ^ 2 * Real.cos (k * a) ^ 2)⁻¹
  | .C =>
      (1 + 2 * m * α ^ 2 / (ℏ ^ 2 * E) *
        (Real.cos (2 * k * a) -
          m * α / (ℏ * k) * Real.sin (2 * k * a)))⁻¹
  | .D =>
      (1 + (m * α / ℏ ^ 2) ^ 2)⁻¹

/-- Answer label recorded by the dataset; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The transmission coefficient supported by the delta matching law.  With
`η = mα/(ℏ²k)` and `ka = k a`, this is

`T = [1 + 4η² (cos(2ka) - η sin(2ka))²]⁻¹`.

Using `ℏ²k² = 2mE`, the prefactor `4η²` is equivalently
`2mα²/(ℏ²E)`.  Unlike the literal source option C, both the inner coupling
and the squared trigonometric factor are dimensionally and algebraically
consistent with `T = 1 / |M₂₂|²`.
-/
def physicallySupportedTransmissionCoefficient
    (setup : DoubleDeltaScatteringSetup) : ℝ :=
  let m := particleMassKilograms setup
  let α := deltaStrengthSI setup
  let ℏ := reducedPlanckSI setup
  let E := incidentEnergyJoules setup
  let k := waveNumberSI setup
  let a := halfSeparationMeters setup
  (1 + 2 * m * α ^ 2 / (ℏ ^ 2 * E) *
    (Real.cos (2 * k * a) -
      m * α / (ℏ ^ 2 * k) * Real.sin (2 * k * a)) ^ 2)⁻¹

/-!
The boundary conditions, free-particle dispersion relation, and transfer laws
determine both local transfer matrices, their ordered total matrix, and the
dimensionally consistent transmission coefficient.  The source's recorded C
label remains separate metadata and is not claimed to be physically correct.

This formalizes `thm:physics:phyx_mini_0602:target`.
-/
theorem problem_phyx_mini_0602
    (setup : DoubleDeltaScatteringSetup)
    (hScenario : MatchesDoubleDeltaScenario setup)
    (hFigure : MatchesSuppliedDoubleDeltaFigure setup)
    (hIncoming : MatchesLeftIncidentScatteringState setup)
    (hPhysical : HasPhysicalDoubleDeltaParameters setup)
    (hPlanck : UsesStandardReducedPlanckConstant setup)
    (hDispersion : SatisfiesFreeParticleDispersionLaw setup)
    (hScattering : SatisfiesDoubleDeltaScatteringLaws setup) :
    setup.firstInteractionMatrix =
        attractiveDeltaTransferMatrix setup (-halfSeparationMeters setup) ∧
      setup.secondInteractionMatrix =
        attractiveDeltaTransferMatrix setup (halfSeparationMeters setup) ∧
      setup.totalTransferMatrix =
        setup.secondInteractionMatrix * setup.firstInteractionMatrix ∧
      setup.totalTransferMatrix =
        explicitDoubleDeltaTransferMatrix setup ∧
      setup.transmissionCoefficient =
        physicallySupportedTransmissionCoefficient setup := by
  have hMatchingUnique
      (positionMeters : ℝ)
      (before after : AmplitudePair)
      (hMatching :
        SatisfiesAttractiveDeltaMatching setup positionMeters before after) :
      after = attractiveDeltaTransferMatrix setup positionMeters *ᵥ before := by
    let k : ℝ := waveNumberSI setup
    let m : ℝ := particleMassKilograms setup
    let α : ℝ := deltaStrengthSI setup
    let ℏ : ℝ := reducedPlanckSI setup
    let η : ℝ := dimensionlessDeltaCoupling setup
    let e : ℂ :=
      Complex.exp (Complex.I * Complex.ofReal (k * positionMeters))
    let f : ℂ :=
      Complex.exp (-Complex.I * Complex.ofReal (k * positionMeters))
    have hk : k ≠ 0 := ne_of_gt hPhysical.waveNumberPositive
    have hℏ : ℏ ≠ 0 := ne_of_gt hPhysical.reducedPlanckActionPositive
    have hη :
        m * α / ℏ ^ 2 / k = η := by
      dsimp [η, dimensionlessDeltaCoupling, m, α, ℏ, k]
      field_simp
    have hContinuous :
        after 0 * e + after 1 * f =
          before 0 * e + before 1 * f := by
      exact hMatching.waveFunctionContinuous
    have hJump :
        Complex.I * Complex.ofReal k *
              (after 0 * e - after 1 * f) -
            Complex.I * Complex.ofReal k *
              (before 0 * e - before 1 * f) =
          Complex.ofReal (-(2 * m * α) / ℏ ^ 2) *
            (before 0 * e + before 1 * f) := by
      exact hMatching.derivativeJump
    have hContinuousZero :
        (after 0 * e - before 0 * e) +
            (after 1 * f - before 1 * f) = 0 := by
      linear_combination hContinuous
    have hDeltaZero :
        Complex.ofReal k * (after 0 * e - before 0 * e) =
          Complex.I * Complex.ofReal (m * α / ℏ ^ 2) *
            (before 0 * e + before 1 * f) := by
      calc
        Complex.ofReal k * (after 0 * e - before 0 * e) =
            (Complex.ofReal k / 2) *
                ((after 0 * e - before 0 * e) +
                  (after 1 * f - before 1 * f)) +
              (-Complex.I / 2) *
                (Complex.I * Complex.ofReal k *
                      (after 0 * e - after 1 * f) -
                    Complex.I * Complex.ofReal k *
                      (before 0 * e - before 1 * f)) := by
              ring_nf
              rw [Complex.I_sq]
              ring
        _ = Complex.I * Complex.ofReal (m * α / ℏ ^ 2) *
              (before 0 * e + before 1 * f) := by
          rw [hContinuousZero, hJump]
          push_cast
          ring
    have hDeltaOne :
        Complex.ofReal k * (after 1 * f - before 1 * f) =
          -Complex.I * Complex.ofReal (m * α / ℏ ^ 2) *
            (before 0 * e + before 1 * f) := by
      calc
        Complex.ofReal k * (after 1 * f - before 1 * f) =
            -Complex.ofReal k * (after 0 * e - before 0 * e) := by
              linear_combination
                Complex.ofReal k * hContinuousZero
        _ = -Complex.I * Complex.ofReal (m * α / ℏ ^ 2) *
              (before 0 * e + before 1 * f) := by
          simpa using congrArg Neg.neg hDeltaZero
    have hDeltaZero' :
        after 0 * e - before 0 * e =
          Complex.I * Complex.ofReal η *
            (before 0 * e + before 1 * f) := by
      rw [← hη]
      push_cast
      apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hk))
      push_cast at hDeltaZero
      rw [hDeltaZero]
      field_simp [Complex.ofReal_ne_zero.mpr hk]
    have hDeltaOne' :
        after 1 * f - before 1 * f =
          -Complex.I * Complex.ofReal η *
            (before 0 * e + before 1 * f) := by
      rw [← hη]
      push_cast
      apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hk))
      push_cast at hDeltaOne
      rw [hDeltaOne]
      field_simp [Complex.ofReal_ne_zero.mpr hk]
    have hNegativePhase :
        Complex.exp
              (-Complex.I *
                Complex.ofReal (2 * k * positionMeters)) *
            e =
          f := by
      dsimp [e, f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hPositivePhase :
        Complex.exp
              (Complex.I *
                Complex.ofReal (2 * k * positionMeters)) *
            f =
          e := by
      dsimp [e, f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hAfterZero :
        after 0 =
          (1 + Complex.I * Complex.ofReal η) * before 0 +
            Complex.I * Complex.ofReal η *
              Complex.exp
                (-Complex.I *
                  Complex.ofReal (2 * k * positionMeters)) *
              before 1 := by
      apply (mul_right_cancel₀ (Complex.exp_ne_zero
        (Complex.I * Complex.ofReal (k * positionMeters))))
      change after 0 * e = _
      calc
        after 0 * e =
            before 0 * e +
              Complex.I * Complex.ofReal η *
                (before 0 * e + before 1 * f) := by
          linear_combination hDeltaZero'
        _ = ((1 + Complex.I * Complex.ofReal η) * before 0 +
              Complex.I * Complex.ofReal η *
                Complex.exp
                  (-Complex.I *
                    Complex.ofReal (2 * k * positionMeters)) *
                before 1) * e := by
          rw [← hNegativePhase]
          ring
    have hAfterOne :
        after 1 =
          -Complex.I * Complex.ofReal η *
              Complex.exp
                (Complex.I *
                  Complex.ofReal (2 * k * positionMeters)) *
              before 0 +
            (1 - Complex.I * Complex.ofReal η) * before 1 := by
      apply (mul_right_cancel₀ (Complex.exp_ne_zero
        (-Complex.I * Complex.ofReal (k * positionMeters))))
      change after 1 * f = _
      calc
        after 1 * f =
            before 1 * f -
              Complex.I * Complex.ofReal η *
                (before 0 * e + before 1 * f) := by
          linear_combination hDeltaOne'
        _ = (-Complex.I * Complex.ofReal η *
                Complex.exp
                  (Complex.I *
                    Complex.ofReal (2 * k * positionMeters)) *
                before 0 +
              (1 - Complex.I * Complex.ofReal η) * before 1) * f := by
          rw [← hPositivePhase]
          ring
    funext i
    fin_cases i
    · simpa [attractiveDeltaTransferMatrix, Matrix.mulVec,
        Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, η, k] using hAfterZero
    · simpa [attractiveDeltaTransferMatrix, Matrix.mulVec,
        Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, η, k] using hAfterOne
  have hFirstInteractionMatrix :
      setup.firstInteractionMatrix =
        attractiveDeltaTransferMatrix setup
          (-halfSeparationMeters setup) := by
    rw [Matrix.ext_iff_mulVec]
    intro amplitudes
    calc
      setup.firstInteractionMatrix *ᵥ amplitudes =
          setup.propagateAcrossM1 amplitudes :=
        (hScattering.firstMatrixActs amplitudes).symm
      _ = attractiveDeltaTransferMatrix setup
            (setup.interactionPositionMeters .firstM1) *ᵥ amplitudes :=
        hMatchingUnique _ _ _
          (hScattering.matchingAtFirstInteraction amplitudes)
      _ = attractiveDeltaTransferMatrix setup
            (-halfSeparationMeters setup) *ᵥ amplitudes := by
        rw [hScenario.firstInteractionAtMinusA]
  have hSecondInteractionMatrix :
      setup.secondInteractionMatrix =
        attractiveDeltaTransferMatrix setup
          (halfSeparationMeters setup) := by
    rw [Matrix.ext_iff_mulVec]
    intro amplitudes
    calc
      setup.secondInteractionMatrix *ᵥ amplitudes =
          setup.propagateAcrossM2 amplitudes :=
        (hScattering.secondMatrixActs amplitudes).symm
      _ = attractiveDeltaTransferMatrix setup
            (setup.interactionPositionMeters .secondM2) *ᵥ amplitudes :=
        hMatchingUnique _ _ _
          (hScattering.matchingAtSecondInteraction amplitudes)
      _ = attractiveDeltaTransferMatrix setup
            (halfSeparationMeters setup) *ᵥ amplitudes := by
        rw [hScenario.secondInteractionAtPlusA]
  have hTotalMatrixProduct :
      setup.totalTransferMatrix =
        setup.secondInteractionMatrix *
          setup.firstInteractionMatrix := by
    rw [Matrix.ext_iff_mulVec]
    intro amplitudes
    calc
      setup.totalTransferMatrix *ᵥ amplitudes =
          setup.propagateAcrossM2
            (setup.propagateAcrossM1 amplitudes) :=
        (hScattering.totalMatrixActs amplitudes).symm
      _ = setup.secondInteractionMatrix *ᵥ
            setup.propagateAcrossM1 amplitudes :=
        hScattering.secondMatrixActs _
      _ = setup.secondInteractionMatrix *ᵥ
            (setup.firstInteractionMatrix *ᵥ amplitudes) := by
        rw [hScattering.firstMatrixActs]
      _ = (setup.secondInteractionMatrix *
            setup.firstInteractionMatrix) *ᵥ amplitudes :=
        Matrix.mulVec_mulVec _ _ _
  have hExplicitProduct :
      attractiveDeltaTransferMatrix setup (halfSeparationMeters setup) *
          attractiveDeltaTransferMatrix setup (-halfSeparationMeters setup) =
        explicitDoubleDeltaTransferMatrix setup := by
    let ka : ℝ := waveNumberSI setup * halfSeparationMeters setup
    have hExpPositive :
        Complex.exp
            (Complex.I *
              (2 * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup))) =
          Complex.cos
              (2 * (Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup))) +
            Complex.sin
                (2 * (Complex.ofReal (waveNumberSI setup) *
                  Complex.ofReal (halfSeparationMeters setup))) *
              Complex.I := by
      rw [show
        Complex.I *
              (2 * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup)) =
            Complex.ofReal (2 * ka) * Complex.I by
          dsimp [ka]
          push_cast
          ring]
      rw [Complex.exp_ofReal_mul_I]
      simp [ka]
    have hExpNegative :
        Complex.exp
            (-(Complex.I *
              (2 * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup)))) =
          Complex.cos
              (2 * (Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup))) -
            Complex.sin
                (2 * (Complex.ofReal (waveNumberSI setup) *
                  Complex.ofReal (halfSeparationMeters setup))) *
              Complex.I := by
      rw [show
        -(Complex.I *
              (2 * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup))) =
            Complex.ofReal (-(2 * ka)) * Complex.I by
          dsimp [ka]
          norm_num [map_neg, map_mul]
          ring]
      rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      simp [ka]
      ring
    have hExpNegativeSquare :
        Complex.exp
              (-(Complex.I * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup) * 2)) ^ 2 =
          Complex.exp
            (-(Complex.I * Complex.ofReal (waveNumberSI setup) *
              Complex.ofReal (halfSeparationMeters setup) * 4)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring
    have hExpPositiveSquare :
        Complex.exp
              (Complex.I * Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup) * 2) ^ 2 =
          Complex.exp
            (Complex.I * Complex.ofReal (waveNumberSI setup) *
              Complex.ofReal (halfSeparationMeters setup) * 4) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.mul_apply, Fin.sum_univ_two,
        attractiveDeltaTransferMatrix, explicitDoubleDeltaTransferMatrix,
        ka]
    · ring_nf
      rw [hExpNegativeSquare, Complex.I_sq]
      ring
    · rw [hExpPositive, hExpNegative]
      ring_nf
      rw [show Complex.I ^ 3 = -Complex.I by
        rw [pow_succ, Complex.I_sq]
        ring]
      ring
    · rw [hExpPositive, hExpNegative]
      ring_nf
      rw [show Complex.I ^ 3 = -Complex.I by
        rw [pow_succ, Complex.I_sq]
        ring]
      ring
    · ring_nf
      rw [hExpPositiveSquare, Complex.I_sq]
      ring
  have hExplicitMatrix :
      setup.totalTransferMatrix =
        explicitDoubleDeltaTransferMatrix setup := by
    rw [hTotalMatrixProduct, hFirstInteractionMatrix,
      hSecondInteractionMatrix]
    exact hExplicitProduct
  have hSingleInteractionDeterminant
      (positionMeters : ℝ) :
      Matrix.det (attractiveDeltaTransferMatrix setup positionMeters) = 1 := by
    have hPhaseCancel :
        Complex.exp
              (-(Complex.I *
                Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal positionMeters * 2)) *
            Complex.exp
              (Complex.I *
                Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal positionMeters * 2) =
          1 := by
      rw [← Complex.exp_add]
      ring_nf
      simp
    rw [Matrix.det_fin_two]
    simp [attractiveDeltaTransferMatrix]
    ring_nf
    rw [mul_assoc, hPhaseCancel, Complex.I_sq]
    ring
  have hTotalDeterminant :
      Matrix.det setup.totalTransferMatrix = 1 := by
    rw [hTotalMatrixProduct, Matrix.det_mul,
      hFirstInteractionMatrix, hSecondInteractionMatrix,
      hSingleInteractionDeterminant, hSingleInteractionDeterminant]
    norm_num
  have hRightAmplitudes :
      setup.rightAmplitudes =
        setup.totalTransferMatrix *ᵥ setup.leftAmplitudes := by
    calc
      setup.rightAmplitudes =
          setup.propagateAcrossM2 setup.middleAmplitudes :=
        hScattering.namedRightAmplitudes
      _ = setup.propagateAcrossM2
            (setup.propagateAcrossM1 setup.leftAmplitudes) := by
        rw [hScattering.namedMiddleAmplitudes]
      _ = setup.totalTransferMatrix *ᵥ setup.leftAmplitudes :=
        hScattering.totalMatrixActs _
  have hTransmittedComponent :
      amplitudeF setup =
        setup.totalTransferMatrix 0 0 * amplitudeA setup +
          setup.totalTransferMatrix 0 1 * amplitudeB setup := by
    have hComponent := congrFun hRightAmplitudes 0
    simpa [amplitudeF, amplitudeA, amplitudeB, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using hComponent
  have hNoIncomingComponent :
      setup.totalTransferMatrix 1 0 * amplitudeA setup +
          setup.totalTransferMatrix 1 1 * amplitudeB setup = 0 := by
    have hComponent := congrFun hRightAmplitudes 1
    have hRightOne :
        setup.rightAmplitudes 1 = 0 := by
      exact hIncoming.noIncomingWaveFromRight
    rw [hRightOne] at hComponent
    simpa [amplitudeA, amplitudeB, Matrix.mulVec,
      Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using hComponent.symm
  have hDeterminantEntries :
      setup.totalTransferMatrix 0 0 *
            setup.totalTransferMatrix 1 1 -
          setup.totalTransferMatrix 0 1 *
            setup.totalTransferMatrix 1 0 =
        1 := by
    simpa [Matrix.det_fin_two] using hTotalDeterminant
  have hLowerRightTimesTransmitted :
      setup.totalTransferMatrix 1 1 * amplitudeF setup =
        amplitudeA setup := by
    calc
      setup.totalTransferMatrix 1 1 * amplitudeF setup =
          setup.totalTransferMatrix 1 1 *
            (setup.totalTransferMatrix 0 0 * amplitudeA setup +
              setup.totalTransferMatrix 0 1 * amplitudeB setup) := by
        rw [hTransmittedComponent]
      _ = (setup.totalTransferMatrix 0 0 *
              setup.totalTransferMatrix 1 1 -
            setup.totalTransferMatrix 0 1 *
              setup.totalTransferMatrix 1 0) * amplitudeA setup +
            setup.totalTransferMatrix 0 1 *
              (setup.totalTransferMatrix 1 0 * amplitudeA setup +
                setup.totalTransferMatrix 1 1 * amplitudeB setup) := by
        ring
      _ = amplitudeA setup := by
        rw [hDeterminantEntries, hNoIncomingComponent]
        ring
  have hLowerRightNonzero :
      setup.totalTransferMatrix 1 1 ≠ 0 := by
    intro hZero
    rw [hZero, zero_mul] at hLowerRightTimesTransmitted
    exact hIncoming.incidentAmplitudeNonzero
      hLowerRightTimesTransmitted.symm
  have hTransmissionAmplitude :
      amplitudeF setup / amplitudeA setup =
        (setup.totalTransferMatrix 1 1)⁻¹ := by
    rw [div_eq_iff hIncoming.incidentAmplitudeNonzero]
    calc
      amplitudeF setup =
          (setup.totalTransferMatrix 1 1)⁻¹ *
            (setup.totalTransferMatrix 1 1 * amplitudeF setup) := by
        field_simp
      _ = (setup.totalTransferMatrix 1 1)⁻¹ * amplitudeA setup := by
        rw [hLowerRightTimesTransmitted]
  have hConjugateDiagonal :
      starRingEnd ℂ (setup.totalTransferMatrix 1 1) =
        setup.totalTransferMatrix 0 0 := by
    have hConjugateExponential :
        starRingEnd ℂ
            (Complex.exp
              (4 * Complex.I *
                (Complex.ofReal (waveNumberSI setup) *
                  Complex.ofReal (halfSeparationMeters setup)))) =
          Complex.exp
            (-(4 * Complex.I *
              (Complex.ofReal (waveNumberSI setup) *
                Complex.ofReal (halfSeparationMeters setup)))) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul, map_ofNat]
      simp
    rw [hExplicitMatrix]
    simp [explicitDoubleDeltaTransferMatrix, map_add, map_mul, map_pow,
      hConjugateExponential]
  have hOffDiagonalProduct :
      setup.totalTransferMatrix 0 1 *
          setup.totalTransferMatrix 1 0 =
        Complex.ofReal
          (4 * dimensionlessDeltaCoupling setup ^ 2 *
            (Real.cos
                (2 * waveNumberSI setup * halfSeparationMeters setup) -
              dimensionlessDeltaCoupling setup *
                Real.sin
                  (2 * waveNumberSI setup *
                    halfSeparationMeters setup)) ^ 2) := by
    rw [hExplicitMatrix]
    simp [explicitDoubleDeltaTransferMatrix]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hLowerRightNormSq :
      Complex.normSq (setup.totalTransferMatrix 1 1) =
        1 + 4 * dimensionlessDeltaCoupling setup ^ 2 *
          (Real.cos
              (2 * waveNumberSI setup * halfSeparationMeters setup) -
            dimensionlessDeltaCoupling setup *
              Real.sin
                (2 * waveNumberSI setup *
                  halfSeparationMeters setup)) ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    calc
      starRingEnd ℂ (setup.totalTransferMatrix 1 1) *
            setup.totalTransferMatrix 1 1 =
          setup.totalTransferMatrix 0 0 *
            setup.totalTransferMatrix 1 1 := by
        rw [hConjugateDiagonal]
      _ = 1 + setup.totalTransferMatrix 0 1 *
            setup.totalTransferMatrix 1 0 := by
        linear_combination hDeterminantEntries
      _ = Complex.ofReal
            (1 + 4 * dimensionlessDeltaCoupling setup ^ 2 *
              (Real.cos
                  (2 * waveNumberSI setup *
                    halfSeparationMeters setup) -
                dimensionlessDeltaCoupling setup *
                  Real.sin
                    (2 * waveNumberSI setup *
                      halfSeparationMeters setup)) ^ 2) := by
        rw [hOffDiagonalProduct]
        push_cast
        ring
  have hTransmissionFromLowerRight :
      setup.transmissionCoefficient =
        (Complex.normSq (setup.totalTransferMatrix 1 1))⁻¹ := by
    calc
      setup.transmissionCoefficient =
          Complex.normSq (amplitudeF setup / amplitudeA setup) :=
        hScattering.transmissionIsAmplitudeNormRatio
      _ = Complex.normSq ((setup.totalTransferMatrix 1 1)⁻¹) := by
        rw [hTransmissionAmplitude]
      _ = (Complex.normSq (setup.totalTransferMatrix 1 1))⁻¹ :=
        Complex.normSq_inv _
  have hMassNonzero :
      particleMassKilograms setup ≠ 0 :=
    ne_of_gt hPhysical.particleMassPositive
  have hPlanckNonzero :
      reducedPlanckSI setup ≠ 0 :=
    ne_of_gt hPhysical.reducedPlanckActionPositive
  have hEnergyNonzero :
      incidentEnergyJoules setup ≠ 0 :=
    ne_of_gt hPhysical.incidentEnergyPositive
  have hWaveNumberNonzero :
      waveNumberSI setup ≠ 0 :=
    ne_of_gt hPhysical.waveNumberPositive
  have hDispersionPrefactor :
      2 * particleMassKilograms setup * deltaStrengthSI setup ^ 2 /
          (reducedPlanckSI setup ^ 2 * incidentEnergyJoules setup) =
        4 *
          (particleMassKilograms setup * deltaStrengthSI setup /
            (reducedPlanckSI setup ^ 2 * waveNumberSI setup)) ^ 2 := by
    field_simp [hMassNonzero, hPlanckNonzero, hEnergyNonzero,
      hWaveNumberNonzero]
    nlinarith [hDispersion.energyWaveNumberRelation]
  have hTransmissionCoefficient :
      setup.transmissionCoefficient =
        physicallySupportedTransmissionCoefficient setup := by
    calc
      setup.transmissionCoefficient =
          (Complex.normSq (setup.totalTransferMatrix 1 1))⁻¹ :=
        hTransmissionFromLowerRight
      _ = (1 + 4 * dimensionlessDeltaCoupling setup ^ 2 *
            (Real.cos
                (2 * waveNumberSI setup *
                  halfSeparationMeters setup) -
              dimensionlessDeltaCoupling setup *
                Real.sin
                  (2 * waveNumberSI setup *
                    halfSeparationMeters setup)) ^ 2)⁻¹ := by
        rw [hLowerRightNormSq]
      _ = physicallySupportedTransmissionCoefficient setup := by
        simp only [physicallySupportedTransmissionCoefficient]
        rw [hDispersionPrefactor, dimensionlessDeltaCoupling]
  exact ⟨hFirstInteractionMatrix, hSecondInteractionMatrix,
    hTotalMatrixProduct, hExplicitMatrix, hTransmissionCoefficient⟩

end PhyXMiniProblems.ProblemPhyXMini0602
