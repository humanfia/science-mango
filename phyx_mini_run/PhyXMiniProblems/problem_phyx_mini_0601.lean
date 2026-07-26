import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Physlib.Mathematics.Distribution.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0601

open Dimension

/-!
# Scattering and transfer matrices for an attractive delta potential

The source describes a localized one-dimensional potential with incoming
amplitudes `A`, `G` and outgoing amplitudes `B`, `F`, then asks for the
scattering matrix of a delta-function well.  Its recorded multiple-choice
answer instead gives the standard transfer-matrix expression
`T_L = 1 / |M₂₂|²`.  Both substantive claims are retained as conclusions.

Physical masses, energies, wave numbers, and delta-well strengths are modeled
as `Dimensionful` quantities.  Real and complex scalars below are explicitly
coherent-SI readouts, normalized wave amplitudes, or dimensionless
probabilities and couplings.

Assumption/target split:

* `MatchesPrimaryScatteringFigure` records only the axes, region labels,
  asymptotic wave labels, arrows, and positive/negative lobes visible in image
  601;
* `MatchesAttractiveDeltaWellScenario`, `SatisfiesFreeParticleDispersionLaw`,
  `SatisfiesAsymptoticWaveForms`, `SatisfiesRegionIISolutionDescription`,
  `SatisfiesDeltaWellBoundaryLaws`, `SatisfiesScatteringMatrixRole`,
  `SatisfiesTransferMatrixLaws`, and `SatisfiesScatteringObservables` are
  setup data or governing laws;
* the explicit delta-well `S`-matrix and the assertion
  `T_L = 1 / |M₂₂|²` occur only in theorem conclusions.  The four unasserted
  answer expressions are retained separately as dataset metadata.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A unit-independent particle mass, of physical dimension `M`. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent one-dimensional wave number, of dimension `L⁻¹`. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-!
The positive strength `α` in the attractive potential `V(x) = -α δ(x-x₀)`.
It has dimensions energy times length, `M L³ T⁻²`.
-/
abbrev DeltaWellStrengthQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Coherent-SI mass readout, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI energy readout, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Coherent-SI wave-number readout, in inverse metres. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- Coherent-SI delta-well strength readout, in joule metres. -/
def deltaWellStrengthInJouleMeters
    (strength : DeltaWellStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Physlib's reduced Planck constant, read in joule seconds. -/
def reducedPlanckConstantInJouleSeconds : ℝ :=
  (Constants.ℏ : ℝ)

/-! ## Figure and wave-component vocabulary -/

/-- The three spatial regions printed under the potential diagram. -/
inductive ScatteringRegion where
  | I
  | II
  | III
  deriving DecidableEq, Repr

/-- Horizontal direction of propagation of a plane-wave component. -/
inductive PropagationDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The four amplitude labels attached to arrows in the primary image. -/
inductive AsymptoticWaveComponent where
  | A
  | B
  | F
  | G
  deriving DecidableEq, Repr

/-- The two axes appearing in the potential diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Literal axis symbols printed in the image. -/
inductive AxisSymbol where
  | x
  | VofX
  deriving DecidableEq, Repr

/-!
Raster-visible qualitative data from image 601.  The image is a generic
localized-potential diagram rather than a literal drawing of a Dirac delta;
the delta-well specialization is therefore kept in a separate scenario law.
-/
structure ScatteringFigure where
  axisSymbol : FigureAxis → AxisSymbol
  regionAt : Fin 3 → ScatteringRegion
  componentRegion : AsymptoticWaveComponent → ScatteringRegion
  componentDirection : AsymptoticWaveComponent → PropagationDirection
  zeroBaselineInRegionIShown : Bool
  localizedPotentialCurveInRegionIIShown : Bool
  positivePotentialLobeInRegionIIShown : Bool
  negativePotentialLobeInRegionIIShown : Bool
  zeroBaselineInRegionIIIShown : Bool

/-! ## Physical setup and source wave functions -/

/--
All quantities required by the prose, the delta-well specialization, and the
four answer choices.  `A`, `G` are incoming amplitudes; `B`, `F` are outgoing.
The distribution field is an SI-coordinate representation of the potential.
-/
structure DeltaWellScatteringSetup where
  particleMass : MassQuantity
  particleEnergy : DimEnergy
  waveNumber : WaveNumberQuantity
  wellStrength : DeltaWellStrengthQuantity
  wellPositionMeters : ℝ
  leftRegionBoundaryMeters : ℝ
  rightRegionBoundaryMeters : ℝ
  potentialEnergyDistributionSI : ℝ →d[ℝ] ℝ
  waveFunction : ℝ → ℂ
  regionIIParticularSolutionF : ℝ → ℂ
  regionIIParticularSolutionG : ℝ → ℂ
  regionIICoefficientC : ℂ
  regionIICoefficientD : ℂ
  incomingAmplitudeA : ℂ
  outgoingAmplitudeB : ℂ
  outgoingAmplitudeF : ℂ
  incomingAmplitudeG : ℂ
  scatteringMatrix : Matrix (Fin 2) (Fin 2) ℂ
  transferMatrix : Matrix (Fin 2) (Fin 2) ℂ
  reflectionCoefficientFromLeft : ℝ
  transmissionCoefficientFromLeft : ℝ
  reflectionCoefficientFromRight : ℝ
  transmissionCoefficientFromRight : ℝ
  figure : ScatteringFigure

/-- The Region-I plane-wave superposition `Aeⁱᵏˣ + Be⁻ⁱᵏˣ`. -/
def regionIPlaneWave
    (setup : DeltaWellScatteringSetup) (xMeters : ℝ) : ℂ :=
  setup.incomingAmplitudeA *
      Complex.exp
        (Complex.I *
          ((waveNumberInInverseMeters setup.waveNumber * xMeters : ℝ) : ℂ)) +
    setup.outgoingAmplitudeB *
      Complex.exp
        (-Complex.I *
          ((waveNumberInInverseMeters setup.waveNumber * xMeters : ℝ) : ℂ))

/-- The Region-III plane-wave superposition `Feⁱᵏˣ + Ge⁻ⁱᵏˣ`. -/
def regionIIIPlaneWave
    (setup : DeltaWellScatteringSetup) (xMeters : ℝ) : ℂ :=
  setup.outgoingAmplitudeF *
      Complex.exp
        (Complex.I *
          ((waveNumberInInverseMeters setup.waveNumber * xMeters : ℝ) : ℂ)) +
    setup.incomingAmplitudeG *
      Complex.exp
        (-Complex.I *
          ((waveNumberInInverseMeters setup.waveNumber * xMeters : ℝ) : ℂ))

/--
Elementary linear independence of the two particular complex-valued
solutions used in Region II.
-/
def AreLinearlyIndependentComplexFunctions
    (f g : ℝ → ℂ) : Prop :=
  ∀ c d : ℂ,
    (∀ x : ℝ, c * f x + d * g x = 0) → c = 0 ∧ d = 0

/-! ## Figure readouts, scenario data, and governing laws -/

/-- Exact qualitative labels and arrow directions visible in image 601. -/
structure MatchesPrimaryScatteringFigure
    (setup : DeltaWellScatteringSetup) : Prop where
  horizontalAxis : setup.figure.axisSymbol .horizontal = .x
  verticalAxis : setup.figure.axisSymbol .vertical = .VofX
  regionsInOrder : setup.figure.regionAt = ![.I, .II, .III]
  componentAInRegionI : setup.figure.componentRegion .A = .I
  componentBInRegionI : setup.figure.componentRegion .B = .I
  componentFInRegionIII : setup.figure.componentRegion .F = .III
  componentGInRegionIII : setup.figure.componentRegion .G = .III
  componentARightward : setup.figure.componentDirection .A = .rightward
  componentBLeftward : setup.figure.componentDirection .B = .leftward
  componentFRightward : setup.figure.componentDirection .F = .rightward
  componentGLeftward : setup.figure.componentDirection .G = .leftward
  regionIBaselineShown : setup.figure.zeroBaselineInRegionIShown = true
  regionIICurveShown :
    setup.figure.localizedPotentialCurveInRegionIIShown = true
  regionIIPositiveLobeShown :
    setup.figure.positivePotentialLobeInRegionIIShown = true
  regionIINegativeLobeShown :
    setup.figure.negativePotentialLobeInRegionIIShown = true
  regionIIIBaselineShown : setup.figure.zeroBaselineInRegionIIIShown = true

/-!
The question's attractive delta-function well, positioned at the origin.  A
Dirac distribution is used instead of replacing the potential with a scalar.
-/
structure MatchesAttractiveDeltaWellScenario
    (setup : DeltaWellScatteringSetup) : Prop where
  wellAtOrigin : setup.wellPositionMeters = 0
  wellInsideRegionII :
    setup.leftRegionBoundaryMeters < setup.wellPositionMeters ∧
      setup.wellPositionMeters < setup.rightRegionBoundaryMeters
  potentialIsAttractiveDelta :
    setup.potentialEnergyDistributionSI =
      (-deltaWellStrengthInJouleMeters setup.wellStrength) •
        Physlib.Distribution.diracDelta ℝ setup.wellPositionMeters

/-- Positive mass, energy, wave number, and nonzero attractive-well strength. -/
structure HasPhysicalDeltaWellParameters
    (setup : DeltaWellScatteringSetup) : Prop where
  massPositive : 0 < massInKilograms setup.particleMass
  energyPositive : 0 < energyInJoules setup.particleEnergy
  waveNumberPositive : 0 < waveNumberInInverseMeters setup.waveNumber
  wellStrengthPositive :
    0 < deltaWellStrengthInJouleMeters setup.wellStrength

/-!
The scalar expression printed on the right-hand side of the source's formula
`k = sqrt (2 m E / ℏ)`.  It is retained as source metadata, not asserted as a
governing law, because it is dimensionally inconsistent.
-/
def sourcePrintedDispersionExpressionSI
    (setup : DeltaWellScatteringSetup) : ℝ :=
  Real.sqrt
    (2 * massInKilograms setup.particleMass *
      energyInJoules setup.particleEnergy /
        reducedPlanckConstantInJouleSeconds)

/-!
The physically standard free-particle dispersion relation
`k² = 2 m E / ℏ²`, stated through coherent-SI readouts.  Unlike the printed
source expression above, both sides have dimensions of inverse metres squared.
-/
def SatisfiesFreeParticleDispersionLaw
    (setup : DeltaWellScatteringSetup) : Prop :=
  waveNumberInInverseMeters setup.waveNumber ^ 2 =
    2 * massInKilograms setup.particleMass *
        energyInJoules setup.particleEnergy /
      reducedPlanckConstantInJouleSeconds ^ 2

/-- The asymptotically free Region-I and Region-III wave forms in the prose. -/
structure SatisfiesAsymptoticWaveForms
    (setup : DeltaWellScatteringSetup) : Prop where
  regionIForm :
    ∀ x : ℝ, x < setup.leftRegionBoundaryMeters →
      setup.waveFunction x = regionIPlaneWave setup x
  regionIIIForm :
    ∀ x : ℝ, setup.rightRegionBoundaryMeters < x →
      setup.waveFunction x = regionIIIPlaneWave setup x

/--
The source's Region-II statement `ψ = C f + D g`, with `f` and `g` linearly
independent particular solutions of the linear second-order equation.
-/
structure SatisfiesRegionIISolutionDescription
    (setup : DeltaWellScatteringSetup) : Prop where
  particularSolutionsIndependent :
    AreLinearlyIndependentComplexFunctions
      setup.regionIIParticularSolutionF setup.regionIIParticularSolutionG
  regionIIForm :
    ∀ x : ℝ,
      setup.leftRegionBoundaryMeters ≤ x →
      x ≤ setup.rightRegionBoundaryMeters →
      setup.waveFunction x =
        setup.regionIICoefficientC * setup.regionIIParticularSolutionF x +
          setup.regionIICoefficientD * setup.regionIIParticularSolutionG x

/--
Dimensionless coupling `η = m α / (ℏ² k)` for an attractive delta well.
-/
def deltaWellCoupling (setup : DeltaWellScatteringSetup) : ℝ :=
  massInKilograms setup.particleMass *
      deltaWellStrengthInJouleMeters setup.wellStrength /
    (reducedPlanckConstantInJouleSeconds ^ 2 *
      waveNumberInInverseMeters setup.waveNumber)

/-!
Continuity of `ψ` and the derivative jump
`ψ'(0⁺)-ψ'(0⁻)=-(2mα/ℏ²)ψ(0)` for every pair of incoming amplitudes.  The
outgoing amplitudes are obtained from the candidate physical `S`-matrix, so
these laws determine that matrix without assuming its requested closed form.
-/
structure SatisfiesDeltaWellBoundaryLaws
    (setup : DeltaWellScatteringSetup) : Prop where
  waveFunctionContinuous :
    ∀ incoming : Fin 2 → ℂ,
      incoming 0 + (Matrix.mulVec setup.scatteringMatrix incoming) 0 =
        (Matrix.mulVec setup.scatteringMatrix incoming) 1 + incoming 1
  derivativeJump :
    ∀ incoming : Fin 2 → ℂ,
      Complex.I * (waveNumberInInverseMeters setup.waveNumber : ℂ) *
          ((Matrix.mulVec setup.scatteringMatrix incoming) 1 - incoming 1 -
            incoming 0 +
              (Matrix.mulVec setup.scatteringMatrix incoming) 0) =
        (-((2 * massInKilograms setup.particleMass *
              deltaWellStrengthInJouleMeters setup.wellStrength /
            reducedPlanckConstantInJouleSeconds ^ 2 : ℝ) : ℂ)) *
          (incoming 0 + (Matrix.mulVec setup.scatteringMatrix incoming) 0)

/-- The actual outgoing vector `(B,F)` equals `S` times the incoming `(A,G)`. -/
structure SatisfiesScatteringMatrixRole
    (setup : DeltaWellScatteringSetup) : Prop where
  outgoingFromIncoming :
    ![setup.outgoingAmplitudeB, setup.outgoingAmplitudeF] =
      Matrix.mulVec setup.scatteringMatrix
        ![setup.incomingAmplitudeA, setup.incomingAmplitudeG]

/-!
Transfer convention `(F,G)ᵀ = M (A,B)ᵀ`, together with the standard unit
determinant law for a localized real one-dimensional potential.
-/
structure SatisfiesTransferMatrixLaws
    (setup : DeltaWellScatteringSetup) : Prop where
  relatesAsymptoticAmplitudes :
    ![setup.outgoingAmplitudeF, setup.incomingAmplitudeG] =
      Matrix.mulVec setup.transferMatrix
        ![setup.incomingAmplitudeA, setup.outgoingAmplitudeB]
  unimodular : Matrix.det setup.transferMatrix = 1

/-- The typical left-incident trial: `G = 0` and the incident wave is nonzero. -/
structure IsLeftIncidentTrial
    (setup : DeltaWellScatteringSetup) : Prop where
  noIncomingWaveFromRight : setup.incomingAmplitudeG = 0
  incidentAmplitudeNonzero : setup.incomingAmplitudeA ≠ 0

/-!
Definitions of the four reflection/transmission coefficients from the source,
plus the amplitude-ratio definition for the actual left-incident trial.
-/
structure SatisfiesScatteringObservables
    (setup : DeltaWellScatteringSetup) : Prop where
  leftReflectionFromS :
    setup.reflectionCoefficientFromLeft =
      Complex.normSq (setup.scatteringMatrix 0 0)
  leftTransmissionFromS :
    setup.transmissionCoefficientFromLeft =
      Complex.normSq (setup.scatteringMatrix 1 0)
  rightReflectionFromS :
    setup.reflectionCoefficientFromRight =
      Complex.normSq (setup.scatteringMatrix 1 1)
  rightTransmissionFromS :
    setup.transmissionCoefficientFromRight =
      Complex.normSq (setup.scatteringMatrix 0 1)
  leftTransmissionFromAmplitudeRatio :
    setup.incomingAmplitudeG = 0 →
    setup.incomingAmplitudeA ≠ 0 →
      setup.transmissionCoefficientFromLeft =
        Complex.normSq
          (setup.outgoingAmplitudeF / setup.incomingAmplitudeA)

/-! ## Multiple-choice expressions and formalization targets -/

/-- Labels attached to the four expressions in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar expression printed beside each answer label. -/
def displayedAnswerValue
    (setup : DeltaWellScatteringSetup) (choice : AnswerChoice) : ℝ :=
  match choice with
  | .A => Complex.normSq (1 / setup.scatteringMatrix 1 1)
  | .B =>
      Complex.normSq
        (setup.transferMatrix 0 1 / setup.transferMatrix 1 1)
  | .C => 1 / Complex.normSq (setup.transferMatrix 1 1)
  | .D => Complex.normSq (Matrix.det setup.transferMatrix)

/-- The modeled left-transmission coefficient agrees with a displayed choice. -/
def MatchesAnswerChoice
    (setup : DeltaWellScatteringSetup) (choice : AnswerChoice) : Prop :=
  setup.transmissionCoefficientFromLeft = displayedAnswerValue setup choice

/-- Recorded dataset metadata; it is not a physical-law premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The delta boundary conditions determine the scattering matrix of the
attractive potential `-α δ(x)`.  This is the construction requested by the
written question, and its closed form occurs only in the conclusion.
-/
lemma attractiveDeltaWell_scatteringMatrix
    (setup : DeltaWellScatteringSetup)
    (hPhysical : HasPhysicalDeltaWellParameters setup)
    (hBoundary : SatisfiesDeltaWellBoundaryLaws setup) :
    setup.scatteringMatrix =
      !![((deltaWellCoupling setup : ℂ) * Complex.I) /
            (1 - (deltaWellCoupling setup : ℂ) * Complex.I),
          1 / (1 - (deltaWellCoupling setup : ℂ) * Complex.I);
          1 / (1 - (deltaWellCoupling setup : ℂ) * Complex.I),
          ((deltaWellCoupling setup : ℂ) * Complex.I) /
            (1 - (deltaWellCoupling setup : ℂ) * Complex.I)] := by
  let k := waveNumberInInverseMeters setup.waveNumber
  let η := deltaWellCoupling setup
  have hk : k ≠ 0 := by
    exact ne_of_gt hPhysical.waveNumberPositive
  have div_mul_identity (m a h k : ℝ) (hk : k ≠ 0) :
      2 * m * a / h ^ 2 = 2 * k * (m * a / (h ^ 2 * k)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    rw [show
      2 * k * (m * a * (k⁻¹ * (h ^ 2)⁻¹)) =
        2 * m * a * (h ^ 2)⁻¹ * (k * k⁻¹) by ring]
    simp [hk]
  have hCoefficient :
      2 * massInKilograms setup.particleMass *
          deltaWellStrengthInJouleMeters setup.wellStrength /
          reducedPlanckConstantInJouleSeconds ^ 2 =
        2 * k * η := by
    simpa [k, η, deltaWellCoupling] using
      div_mul_identity
        (massInKilograms setup.particleMass)
        (deltaWellStrengthInJouleMeters setup.wellStrength)
        reducedPlanckConstantInJouleSeconds
        (waveNumberInInverseMeters setup.waveNumber)
        hk
  have hDenominator :
      (1 - (η : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hContinuousLeft :
      1 + setup.scatteringMatrix 0 0 =
        setup.scatteringMatrix 1 0 := by
    simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead] using
      hBoundary.waveFunctionContinuous ![1, 0]
  have hDerivativeLeft :
      Complex.I * (k : ℂ) *
          (setup.scatteringMatrix 1 0 - 1 +
            setup.scatteringMatrix 0 0) =
        (-((2 * k * η : ℝ) : ℂ)) *
          (1 + setup.scatteringMatrix 0 0) := by
    have h := hBoundary.derivativeJump ![1, 0]
    rw [hCoefficient] at h
    simpa [k, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead] using h
  have solveLeft (s00 s10 : ℂ)
      (hContinuous : 1 + s00 = s10)
      (hDerivative :
        Complex.I * (k : ℂ) * (s10 - 1 + s00) =
          (-((2 * k * η : ℝ) : ℂ)) * (1 + s00)) :
      s00 = (η : ℂ) * Complex.I / (1 - (η : ℂ) * Complex.I) ∧
        s10 = 1 / (1 - (η : ℂ) * Complex.I) := by
    have hkComplex : (k : ℂ) ≠ 0 := by
      exact_mod_cast hk
    rw [← hContinuous] at hDerivative
    push_cast at hDerivative
    have hCancel :
        (k : ℂ) * (2 * (Complex.I * s00)) =
          (k : ℂ) * (2 * (-(η : ℂ) * (1 + s00))) := by
      linear_combination hDerivative
    have hTwice := mul_left_cancel₀ hkComplex hCancel
    have hRelation :
        Complex.I * s00 = -(η : ℂ) * (1 + s00) := by
      linear_combination (2 : ℂ)⁻¹ * hTwice
    have hRelationI :=
      congrArg (fun z : ℂ => Complex.I * z) hRelation
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul] at hRelationI
    constructor
    · field_simp [hDenominator]
      linear_combination -hRelationI
    · rw [← hContinuous]
      field_simp [hDenominator]
      linear_combination -hRelationI
  have hContinuousRight :
      setup.scatteringMatrix 0 1 =
        setup.scatteringMatrix 1 1 + 1 := by
    simpa [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using
      hBoundary.waveFunctionContinuous ![0, 1]
  have hDerivativeRight :
      Complex.I * (k : ℂ) *
          (setup.scatteringMatrix 1 1 - 1 +
            setup.scatteringMatrix 0 1) =
        (-((2 * k * η : ℝ) : ℂ)) *
          setup.scatteringMatrix 0 1 := by
    have h := hBoundary.derivativeJump ![0, 1]
    rw [hCoefficient] at h
    simpa [k, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using h
  have solveRight (s01 s11 : ℂ)
      (hContinuous : s01 = s11 + 1)
      (hDerivative :
        Complex.I * (k : ℂ) * (s11 - 1 + s01) =
          (-((2 * k * η : ℝ) : ℂ)) * s01) :
      s01 = 1 / (1 - (η : ℂ) * Complex.I) ∧
        s11 = (η : ℂ) * Complex.I /
          (1 - (η : ℂ) * Complex.I) := by
    have hkComplex : (k : ℂ) ≠ 0 := by
      exact_mod_cast hk
    have hs11 : s11 = s01 - 1 := by
      linear_combination -hContinuous
    rw [hs11] at hDerivative
    push_cast at hDerivative
    have hCancel :
        (k : ℂ) * (2 * (Complex.I * (s01 - 1))) =
          (k : ℂ) * (2 * (-(η : ℂ) * s01)) := by
      linear_combination hDerivative
    have hTwice := mul_left_cancel₀ hkComplex hCancel
    have hRelation :
        Complex.I * (s01 - 1) = -(η : ℂ) * s01 := by
      linear_combination (2 : ℂ)⁻¹ * hTwice
    have hRelationI :=
      congrArg (fun z : ℂ => Complex.I * z) hRelation
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul] at hRelationI
    constructor
    · field_simp [hDenominator]
      linear_combination -hRelationI
    · rw [hs11]
      field_simp [hDenominator]
      linear_combination -hRelationI
  obtain ⟨h00, h10⟩ :=
    solveLeft
      (setup.scatteringMatrix 0 0)
      (setup.scatteringMatrix 1 0)
      hContinuousLeft hDerivativeLeft
  obtain ⟨h01, h11⟩ :=
    solveRight
      (setup.scatteringMatrix 0 1)
      (setup.scatteringMatrix 1 1)
      hContinuousRight hDerivativeRight
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [η] using h00
  · simpa [η] using h01
  · simpa [η] using h10
  · simpa [η] using h11

/-!
With the convention `(F,G)ᵀ = M(A,B)ᵀ`, left incidence and `det M = 1`
give the recorded transmission formula.  Neither this formula nor answer C is
a field of the transfer or observable laws.
-/
lemma leftTransmission_transferMatrixFormula
    (setup : DeltaWellScatteringSetup)
    (hLeft : IsLeftIncidentTrial setup)
    (hTransfer : SatisfiesTransferMatrixLaws setup)
    (hObservables : SatisfiesScatteringObservables setup) :
    setup.transmissionCoefficientFromLeft =
      1 / Complex.normSq (setup.transferMatrix 1 1) := by
  have hF := congrFun hTransfer.relatesAsymptoticAmplitudes 0
  have hG := congrFun hTransfer.relatesAsymptoticAmplitudes 1
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at hF hG
  rw [hLeft.noIncomingWaveFromRight] at hG
  have hDet := hTransfer.unimodular
  rw [Matrix.det_fin_two] at hDet
  have hM11 : setup.transferMatrix 1 1 ≠ 0 := by
    intro h11
    have hM10 : setup.transferMatrix 1 0 = 0 := by
      rw [h11] at hG
      simp only [zero_mul, add_zero] at hG
      rcases mul_eq_zero.mp hG.symm with h | h
      · exact h
      · exact (hLeft.incidentAmplitudeNonzero h).elim
    rw [h11, hM10] at hDet
    norm_num at hDet
  have hMFA :
      setup.transferMatrix 1 1 * setup.outgoingAmplitudeF =
        setup.incomingAmplitudeA := by
    linear_combination
      setup.transferMatrix 1 1 * hF -
        setup.transferMatrix 0 1 * hG +
        setup.incomingAmplitudeA * hDet
  have hRatio :
      setup.outgoingAmplitudeF / setup.incomingAmplitudeA =
        1 / setup.transferMatrix 1 1 := by
    field_simp [hLeft.incidentAmplitudeNonzero, hM11]
    linear_combination hMFA
  rw [hObservables.leftTransmissionFromAmplitudeRatio
    hLeft.noIncomingWaveFromRight hLeft.incidentAmplitudeNonzero,
    hRatio, Complex.normSq_div]
  norm_num

/-!
For the delta well and the scattering layout shown in image 601, the governing
laws yield both the requested `S`-matrix construction and the expression
recorded as answer C.

This formalizes `thm:physics:phyx_mini_0601:target`.
-/
theorem problem_phyx_mini_0601
    (setup : DeltaWellScatteringSetup)
    (hFigure : MatchesPrimaryScatteringFigure setup)
    (hScenario : MatchesAttractiveDeltaWellScenario setup)
    (hPhysical : HasPhysicalDeltaWellParameters setup)
    (hDispersion : SatisfiesFreeParticleDispersionLaw setup)
    (hAsymptotic : SatisfiesAsymptoticWaveForms setup)
    (hRegionII : SatisfiesRegionIISolutionDescription setup)
    (hBoundary : SatisfiesDeltaWellBoundaryLaws setup)
    (hScattering : SatisfiesScatteringMatrixRole setup)
    (hTransfer : SatisfiesTransferMatrixLaws setup)
    (hLeft : IsLeftIncidentTrial setup)
    (hObservables : SatisfiesScatteringObservables setup) :
    setup.scatteringMatrix =
        !![((deltaWellCoupling setup : ℂ) * Complex.I) /
              (1 - (deltaWellCoupling setup : ℂ) * Complex.I),
            1 / (1 - (deltaWellCoupling setup : ℂ) * Complex.I);
            1 / (1 - (deltaWellCoupling setup : ℂ) * Complex.I),
            ((deltaWellCoupling setup : ℂ) * Complex.I) /
              (1 - (deltaWellCoupling setup : ℂ) * Complex.I)] ∧
      setup.transmissionCoefficientFromLeft =
        1 / Complex.normSq (setup.transferMatrix 1 1) ∧
      MatchesAnswerChoice setup .C ∧
      recordedDatasetAnswer = .C := by
  have hMatrix :=
    attractiveDeltaWell_scatteringMatrix setup hPhysical hBoundary
  have hTransmission :=
    leftTransmission_transferMatrixFormula
      setup hLeft hTransfer hObservables
  refine ⟨hMatrix, hTransmission, ?_, rfl⟩
  simpa [MatchesAnswerChoice, displayedAnswerValue] using hTransmission

end PhyXMiniProblems.ProblemPhyXMini0601
