import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.QuantumMechanics.FiniteTarget
import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
import Physlib.Relativity.PauliMatrices.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0543

/-!
# Spin precession in a uniform z-directed magnetic field

A spin-`1/2` particle is prepared in the `x`-down state, evolves in the
uniform field `B₀ ẑ`, and is then measured along the `x`-axis. Physlib's
two-dimensional finite Hilbert space represents the spin state,
`FiniteTarget.timeEvolution` supplies Hamiltonian time evolution, and the
Pauli matrix `σ₃` represents the z-directed Zeeman coupling.

Scalar fields whose names end in `Tesla`, `JoulesPerTesla`, `Seconds`, or
`RadiansPerSecond` are coherent SI readouts of the corresponding physical
quantities. The actual magnetic field remains a Physlib magnetic-field
object rather than being collapsed to a real scalar.
-/

/-! ## Spin states and spatial directions -/

/-- The two-dimensional Hilbert space of a spin-`1/2` degree of freedom. -/
abbrev SpinHalfState : Type :=
  QuantumMechanics.FiniteHilbertSpace (Fin 2)

/-- The standard spin-z basis, with index `0` for up and `1` for down. -/
def spinZBasis : Module.Basis (Fin 2) ℂ SpinHalfState :=
  (QuantumMechanics.FiniteHilbertSpace.basisFun (Fin 2)).toBasis

/-- The normalized state `|+⟩_z`. -/
def spinZUpState : SpinHalfState := spinZBasis (0 : Fin 2)

/-- The normalized state `|-⟩_z`. -/
def spinZDownState : SpinHalfState := spinZBasis (1 : Fin 2)

/-- The normalized state `|+⟩_x = (|+⟩_z + |-⟩_z)/√2`. -/
def spinXUpState : SpinHalfState :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (spinZUpState + spinZDownState)

/-- The normalized state `|-⟩_x = (|+⟩_z - |-⟩_z)/√2`. -/
def spinXDownState : SpinHalfState :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (spinZUpState - spinZDownState)

/-- The unit coordinate vector `ẑ` in three-dimensional Euclidean space. -/
def zDirection : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (2 : Fin 3) 1

/-! ## Figure vocabulary -/

/-- The spin axes printed in the two analyzers and central field symbol. -/
inductive SpinAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

/-- The two outcomes of a Stern--Gerlach spin measurement. -/
inductive SpinOutcome where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

/-- Vertical positions of paths and output boxes in the supplied diagram. -/
inductive FigureBranchPosition where
  | upper
  | lower
  deriving DecidableEq, Repr

/-!
The apparatus information visible in image 543. The glyph `42` beside the
central `Z` is stored as a raw optional natural-number readout because the
source gives it no unit or physical role.
-/
structure SpinPrecessionFigure where
  sourceBeamShown : Bool
  preparationAnalyzerAxis : SpinAxis
  selectedPreparationOutcome : SpinOutcome
  fieldRegionAxis : SpinAxis
  centralNumericGlyph : Option Nat
  measurementAnalyzerAxis : SpinAxis
  outputBranchPosition : SpinOutcome → FigureBranchPosition
  resultBoxIsBlank : SpinOutcome → Bool
  questionMarkShown : SpinOutcome → Bool

/-! ## Experiment, scenario data, and governing laws -/

/-!
The physical experiment. `magneticFieldMagnitudeTesla` is the scalar `B₀`
readout, while `appliedMagneticField` retains the full spacetime-dependent
Physlib field. The probability observable is independent data until Born's
rule below relates it to the evolved state.
-/
structure SpinPrecessionExperiment where
  quantumSystem : QuantumMechanics.FiniteTarget SpinHalfState 2
  initialState : SpinHalfState
  appliedMagneticField : Electromagnetism.MagneticField 3
  magneticFieldMagnitudeTesla : ℝ
  magneticMomentMagnitudeJoulesPerTesla : ℝ
  larmorAngularFrequencyRadiansPerSecond : ℝ
  probabilityOfSpinUpAlongX : ℝ → ℝ
  figure : SpinPrecessionFigure

/-- Hamiltonian evolution of the prepared state after the given SI time. -/
def evolvedState
    (experiment : SpinPrecessionExperiment)
    (elapsedTimeSeconds : ℝ) : SpinHalfState :=
  experiment.quantumSystem.timeEvolution elapsedTimeSeconds
    experiment.initialState

/-- The prose preparation condition: the entering particle is in `|-⟩_x`. -/
structure MatchesSpinHalfPreparation
    (experiment : SpinPrecessionExperiment) : Prop where
  initialStateIsXDown : experiment.initialState = spinXDownState

/-!
The uniform-field statement `B(τ,r) = B₀ ẑ`. The vector values of Physlib's
field are interpreted here as tesla-coordinate readouts.
-/
structure IsUniformAppliedFieldAlongZ
    (experiment : SpinPrecessionExperiment) : Prop where
  fieldAtEverySpacetimePoint :
    ∀ spacetimeTime position,
      experiment.appliedMagneticField spacetimeTime position =
        experiment.magneticFieldMagnitudeTesla • zDirection

/-!
Exact qualitative and label information transcribed from the supplied
apparatus diagram. No output probability or answer choice occurs here.
-/
structure MatchesSuppliedSpinPrecessionFigure
    (experiment : SpinPrecessionExperiment) : Prop where
  sourceBeamIsShown : experiment.figure.sourceBeamShown = true
  firstAnalyzerIsX : experiment.figure.preparationAnalyzerAxis = .x
  lowerXBranchIsSelected :
    experiment.figure.selectedPreparationOutcome = .down
  centralRegionIsZDirected : experiment.figure.fieldRegionAxis = .z
  centralAuxiliaryGlyphReads42 :
    experiment.figure.centralNumericGlyph = some 42
  finalAnalyzerIsX : experiment.figure.measurementAnalyzerAxis = .x
  upOutcomeUsesUpperBranch :
    experiment.figure.outputBranchPosition .up = .upper
  downOutcomeUsesLowerBranch :
    experiment.figure.outputBranchPosition .down = .lower
  bothResultBoxesAreBlank :
    ∀ outcome, experiment.figure.resultBoxIsBlank outcome = true
  bothOutputsCarryQuestionMarks :
    ∀ outcome, experiment.figure.questionMarkShown outcome = true

/-- Positivity conditions for the field, magnetic moment, and precession rate. -/
structure HasPhysicalSpinPrecessionParameters
    (experiment : SpinPrecessionExperiment) : Prop where
  positiveFieldMagnitude : 0 < experiment.magneticFieldMagnitudeTesla
  positiveMagneticMomentMagnitude :
    0 < experiment.magneticMomentMagnitudeJoulesPerTesla
  positiveLarmorAngularFrequency :
    0 < experiment.larmorAngularFrequencyRadiansPerSecond

/-!
The Zeeman Hamiltonian `H = - μ B₀ σ_z`, expressed in the standard spin-z
basis, together with `ℏ ω₀ = 2 μ B₀`. These are governing relations and do
not assert the requested transition probability.
-/
structure SatisfiesZeemanHamiltonian
    (experiment : SpinPrecessionExperiment) : Prop where
  hamiltonianMatrixIsZeemanCoupling :
    LinearMap.toMatrix spinZBasis spinZBasis
        experiment.quantumSystem.Ham.toLinearMap =
      ((-(experiment.magneticMomentMagnitudeJoulesPerTesla *
          experiment.magneticFieldMagnitudeTesla) : ℝ) : ℂ) •
        PauliMatrix.pauliMatrix (Sum.inr (2 : Fin 3))
  larmorFrequencyRelation :
    (Constants.ℏ : ℝ) *
        experiment.larmorAngularFrequencyRadiansPerSecond =
      2 * experiment.magneticMomentMagnitudeJoulesPerTesla *
        experiment.magneticFieldMagnitudeTesla

/-!
Born's rule for the `x`-up projector at every time. It relates the independent
probability observable to the squared transition amplitude and records the
usual probability bounds. It is not specialized to a sine formula.
-/
structure SatisfiesBornRuleForXSpinMeasurement
    (experiment : SpinPrecessionExperiment) : Prop where
  probabilityIsSquaredTransitionAmplitude :
    ∀ elapsedTimeSeconds : ℝ,
      experiment.probabilityOfSpinUpAlongX elapsedTimeSeconds =
        Complex.normSq
          (inner ℂ spinXUpState
            (evolvedState experiment elapsedTimeSeconds))
  probabilityBounds : ∀ elapsedTimeSeconds : ℝ,
    0 ≤ experiment.probabilityOfSpinUpAlongX elapsedTimeSeconds ∧
      experiment.probabilityOfSpinUpAlongX elapsedTimeSeconds ≤ 1

/-! ## Displayed choices and current target -/

/-- Labels of the four expressions displayed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Half of the accumulated Larmor phase, the argument used in all choices. -/
def halfLarmorPhase
    (angularFrequencyRadiansPerSecond elapsedTimeSeconds : ℝ) : ℝ :=
  angularFrequencyRadiansPerSecond * elapsedTimeSeconds / 2

/-- The four dimensionless probability expressions printed in the source. -/
def displayedProbability
    (choice : AnswerChoice)
    (angularFrequencyRadiansPerSecond elapsedTimeSeconds : ℝ) : ℝ :=
  let phase := halfLarmorPhase
    angularFrequencyRadiansPerSecond elapsedTimeSeconds
  match choice with
  | .A => Real.cot phase ^ 2
  | .B => Real.tan phase ^ 2
  | .C => Real.cos phase ^ 2
  | .D => Real.sin phase ^ 2

/-!
The Zeeman evolution of `|-⟩_x` has `x`-up transition amplitude
`i sin(ω₀ t/2)`. This is a derived intermediate statement, not a premise.
-/
lemma transitionAmplitudeToXUp
    (experiment : SpinPrecessionExperiment)
    (hPreparation : MatchesSpinHalfPreparation experiment)
    (hZeeman : SatisfiesZeemanHamiltonian experiment)
    (elapsedTimeSeconds : ℝ) :
    inner ℂ spinXUpState (evolvedState experiment elapsedTimeSeconds) =
      Complex.I *
        (Real.sin
          (halfLarmorPhase
            experiment.larmorAngularFrequencyRadiansPerSecond
            elapsedTimeSeconds) : ℂ) := by
  let phase := halfLarmorPhase
    experiment.larmorAngularFrequencyRadiansPerSecond elapsedTimeSeconds
  let matrixRep :
      (SpinHalfState →L[ℂ] SpinHalfState) ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    (Module.End.toContinuousLinearMap SpinHalfState).symm.trans
      (LinearMap.toMatrixAlgEquiv spinZBasis)
  letI : NormedAlgebra ℚ (SpinHalfState →L[ℂ] SpinHalfState) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  have hphase :
      experiment.magneticMomentMagnitudeJoulesPerTesla *
          experiment.magneticFieldMagnitudeTesla * elapsedTimeSeconds /
            (Constants.ℏ : ℝ) = phase := by
    apply (div_eq_iff Constants.ℏ_ne_zero).2
    dsimp [phase, halfLarmorPhase]
    have hMomentField :
        experiment.magneticMomentMagnitudeJoulesPerTesla *
            experiment.magneticFieldMagnitudeTesla =
          (Constants.ℏ : ℝ) *
              experiment.larmorAngularFrequencyRadiansPerSecond / 2 := by
      nlinarith [hZeeman.larmorFrequencyRelation]
    rw [hMomentField]
    ring
  have hCoefficientPos :
      Complex.I * (elapsedTimeSeconds : ℂ) / ((Constants.ℏ : ℝ) : ℂ) *
          ((experiment.magneticMomentMagnitudeJoulesPerTesla *
            experiment.magneticFieldMagnitudeTesla : ℝ) : ℂ) =
        Complex.I * (phase : ℂ) := by
    rw [← hphase]
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    push_cast
    field_simp
  have hCoefficientPos' :
      Complex.I * (elapsedTimeSeconds : ℂ) / ((Constants.ℏ : ℝ) : ℂ) *
          ((experiment.magneticMomentMagnitudeJoulesPerTesla : ℂ) *
            (experiment.magneticFieldMagnitudeTesla : ℂ)) =
        Complex.I * (phase : ℂ) := by
    simpa only [Complex.ofReal_mul] using hCoefficientPos
  have hHamMatrix :
      matrixRep experiment.quantumSystem.Ham =
        ((-(experiment.magneticMomentMagnitudeJoulesPerTesla *
          experiment.magneticFieldMagnitudeTesla) : ℝ) : ℂ) •
          PauliMatrix.pauliMatrix (Sum.inr (2 : Fin 3)) := by
    change LinearMap.toMatrix spinZBasis spinZBasis
        experiment.quantumSystem.Ham.toLinearMap = _
    exact hZeeman.hamiltonianMatrixIsZeemanCoupling
  have hGenerator :
      matrixRep
          ((-(Complex.I * (elapsedTimeSeconds : ℂ) /
            ((Constants.ℏ : ℝ) : ℂ))) • experiment.quantumSystem.Ham) =
        Matrix.diagonal
          ![Complex.I * (phase : ℂ), -(Complex.I * (phase : ℂ))] := by
    rw [map_smul, hHamMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PauliMatrix.pauliMatrix, hCoefficientPos']
  have hEvolutionMatrixRep :
      matrixRep (experiment.quantumSystem.timeEvolution elapsedTimeSeconds) =
        Matrix.diagonal
          ![Complex.exp (Complex.I * (phase : ℂ)),
            Complex.exp (-(Complex.I * (phase : ℂ)))] := by
    calc
      matrixRep (experiment.quantumSystem.timeEvolution elapsedTimeSeconds) =
          matrixRep
            (NormedSpace.exp
              ((-(Complex.I * (elapsedTimeSeconds : ℂ) /
                ((Constants.ℏ : ℝ) : ℂ))) • experiment.quantumSystem.Ham)) := rfl
      _ = NormedSpace.exp
          (matrixRep
            ((-(Complex.I * (elapsedTimeSeconds : ℂ) /
              ((Constants.ℏ : ℝ) : ℂ))) • experiment.quantumSystem.Ham)) :=
        NormedSpace.map_exp matrixRep
          matrixRep.toLinearMap.continuous_of_finiteDimensional _
      _ = _ := by
        rw [hGenerator, Matrix.exp_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Complex.exp_eq_exp_ℂ]
  have hEvolutionMatrix :
      LinearMap.toMatrix spinZBasis spinZBasis
          (experiment.quantumSystem.timeEvolution elapsedTimeSeconds).toLinearMap =
        Matrix.diagonal
          ![Complex.exp (Complex.I * (phase : ℂ)),
            Complex.exp (-(Complex.I * (phase : ℂ)))] := by
    change matrixRep (experiment.quantumSystem.timeEvolution elapsedTimeSeconds) = _
    exact hEvolutionMatrixRep
  have hEvolvedState :
      evolvedState experiment elapsedTimeSeconds =
        (((1 / Real.sqrt 2 : ℝ) : ℂ)) •
          (Complex.exp (Complex.I * (phase : ℂ)) • spinZUpState -
            Complex.exp (-(Complex.I * (phase : ℂ))) • spinZDownState) := by
    apply spinZBasis.repr.injective
    apply Finsupp.ext
    intro i
    have hi := congrFun
      (LinearMap.toMatrix_mulVec_repr spinZBasis spinZBasis
        (experiment.quantumSystem.timeEvolution elapsedTimeSeconds).toLinearMap
        experiment.initialState) i
    rw [hPreparation.initialStateIsXDown, hEvolutionMatrix] at hi
    change
      (spinZBasis.repr
        (experiment.quantumSystem.timeEvolution elapsedTimeSeconds
          experiment.initialState)) i = _
    rw [hPreparation.initialStateIsXDown]
    calc
      _ = Matrix.mulVec (Matrix.diagonal
          ![Complex.exp (Complex.I * (phase : ℂ)),
            Complex.exp (-(Complex.I * (phase : ℂ)))])
            (⇑(spinZBasis.repr spinXDownState)) i := hi.symm
      _ = _ := by
        fin_cases i <;>
          simp [spinXDownState, spinZUpState, spinZDownState, Matrix.mulVec]
  have hExpPos :
      Complex.exp (Complex.I * (phase : ℂ)) =
        (Real.cos phase : ℂ) + (Real.sin phase : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
  have hExpNeg :
      Complex.exp (-(Complex.I * (phase : ℂ))) =
        (Real.cos phase : ℂ) - (Real.sin phase : ℂ) * Complex.I := by
    rw [show -(Complex.I * (phase : ℂ)) = ((-phase : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hEvolvedState]
  rw [hExpPos, hExpNeg]
  simp [spinXUpState, spinZUpState, spinZDownState, spinZBasis]
  have hsqrtC : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    norm_cast
    norm_num
  field_simp
  rw [hsqrtC]
  ring

/-!
Blueprint: `thm:physics:phyx_mini_0543:target`.

For every nonnegative elapsed time, measuring spin up along `x` has
probability `sin²(ω₀ t/2)`, which is displayed as choice D.
-/
theorem probabilityOfMeasuringSpinXUpAfterTime
    (experiment : SpinPrecessionExperiment)
    (hPreparation : MatchesSpinHalfPreparation experiment)
    (hUniformField : IsUniformAppliedFieldAlongZ experiment)
    (hFigure : MatchesSuppliedSpinPrecessionFigure experiment)
    (hPhysical : HasPhysicalSpinPrecessionParameters experiment)
    (hZeeman : SatisfiesZeemanHamiltonian experiment)
    (hBorn : SatisfiesBornRuleForXSpinMeasurement experiment) :
    ∀ elapsedTimeSeconds : ℝ, 0 ≤ elapsedTimeSeconds →
      experiment.probabilityOfSpinUpAlongX elapsedTimeSeconds =
          Real.sin
            (halfLarmorPhase
              experiment.larmorAngularFrequencyRadiansPerSecond
              elapsedTimeSeconds) ^ 2 ∧
        experiment.probabilityOfSpinUpAlongX elapsedTimeSeconds =
          displayedProbability .D
            experiment.larmorAngularFrequencyRadiansPerSecond
            elapsedTimeSeconds := by
  intro elapsedTimeSeconds _
  rw [hBorn.probabilityIsSquaredTransitionAmplitude,
    transitionAmplitudeToXUp experiment hPreparation hZeeman elapsedTimeSeconds]
  have hnormSq :
      Complex.normSq
          (Complex.I *
            (Real.sin
              (halfLarmorPhase
                experiment.larmorAngularFrequencyRadiansPerSecond
                elapsedTimeSeconds) : ℂ)) =
        Real.sin
            (halfLarmorPhase
              experiment.larmorAngularFrequencyRadiansPerSecond
              elapsedTimeSeconds) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul]
    ring
  rw [hnormSq]
  constructor
  · rfl
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0543
