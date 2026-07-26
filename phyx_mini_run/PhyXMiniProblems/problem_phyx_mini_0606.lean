import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Relativity.PauliMatrices.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0606

/-!
# Antiferromagnetic spin-1/2 triangle

Three spin-`1/2` particles occupy the vertices of a triangle.  Every pair of
vertices is joined by the same positive Heisenberg exchange coupling.  The
state space below is the eight-dimensional finite Hilbert space whose standard
basis records the three local spin-z outcomes.

The Physlib constant `Constants.ℏ` is measured in joule-seconds.  Consequently
`exchangeCouplingJoulesPerActionSquared` has the dimensional role energy per
action squared, the local spin matrices have the dimension of action, and the
Hamiltonian eigenvalues are energy readouts in joules.
-/

/-! ## Triangle and figure vocabulary -/

/-- The three particle sites, named by the labels printed in the diagram. -/
inductive TriangleSite where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- Qualitative positions of the three nodes in the supplied figure. -/
inductive TriangleFigurePosition where
  | bottomLeft
  | bottomRight
  | top
  deriving DecidableEq, Repr

/-- The vertical spin-arrow glyphs that can be printed at a node. -/
inductive VerticalSpinArrow where
  | up
  | down
  deriving DecidableEq, Repr

/--
Raw information carried by the triangular illustration.  The arrow field is
figure annotation only; it is not asserted to be a simultaneous eigenstate of
the frustrated quantum Hamiltonian.
-/
structure SpinTriangleFigure where
  position : TriangleSite → TriangleFigurePosition
  printedLabel : TriangleSite → ℕ
  verticalArrow : TriangleSite → Option VerticalSpinArrow
  bondShown : TriangleSite → TriangleSite → Prop

/--
Exact qualitative transcription of image 606: a complete three-node triangle,
with no arrow at node 1, a down arrow at node 2, and an up arrow at node 3.
-/
structure MatchesSuppliedSpinTriangleFigure
    (figure : SpinTriangleFigure) : Prop where
  nodeOneIsBottomLeft : figure.position .one = .bottomLeft
  nodeTwoIsBottomRight : figure.position .two = .bottomRight
  nodeThreeIsTop : figure.position .three = .top
  nodeOneLabel : figure.printedLabel .one = 1
  nodeTwoLabel : figure.printedLabel .two = 2
  nodeThreeLabel : figure.printedLabel .three = 3
  nodeOneHasNoArrow : figure.verticalArrow .one = none
  nodeTwoArrowPointsDown : figure.verticalArrow .two = some .down
  nodeThreeArrowPointsUp : figure.verticalArrow .three = some .up
  completeTriangularBondGraph :
    ∀ first second, figure.bondShown first second ↔ first ≠ second

/-! ## Three-spin Hilbert space and local spin operators -/

/--
A standard-basis label `|s₁,s₂,s₃⟩`, with each `Fin 2` factor carrying one
spin-`1/2` degree of freedom.
-/
abbrev ThreeSpinBasis := Fin 2 × (Fin 2 × Fin 2)

/-- The eight-dimensional Hilbert space of three distinguishable spin halves. -/
abbrev ThreeSpinState : Type :=
  QuantumMechanics.FiniteHilbertSpace ThreeSpinBasis

/-- The standard product basis of the three-spin Hilbert space. -/
def threeSpinBasis : Module.Basis ThreeSpinBasis ℂ ThreeSpinState :=
  (QuantumMechanics.FiniteHilbertSpace.basisFun ThreeSpinBasis).toBasis

/-- Cartesian components used in the Heisenberg spin dot product. -/
inductive SpinAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Index of a Cartesian spin component in Physlib's Pauli-matrix family. -/
def SpinAxis.toFin3 : SpinAxis → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

/-- The Pauli matrix associated with a Cartesian spin axis. -/
def pauliForAxis (axis : SpinAxis) : Matrix (Fin 2) (Fin 2) ℂ :=
  PauliMatrix.pauliMatrix (Sum.inr axis.toFin3)

/-- Complex-valued Kronecker delta for unchanged spectator spins. -/
def spinKroneckerDelta (first second : Fin 2) : ℂ :=
  if first = second then 1 else 0

/--
The matrix of the local component `S_site^axis = (ℏ/2) σ_axis`, tensored with
the identity on the two spectator sites.
-/
def localSpinComponentMatrix
    (site : TriangleSite)
    (axis : SpinAxis) : Matrix ThreeSpinBasis ThreeSpinBasis ℂ :=
  fun row column =>
    let halfHbar : ℂ := (((Constants.ℏ : ℝ) / 2 : ℝ) : ℂ)
    match site with
    | .one =>
        halfHbar * pauliForAxis axis row.1 column.1 *
          spinKroneckerDelta row.2.1 column.2.1 *
          spinKroneckerDelta row.2.2 column.2.2
    | .two =>
        halfHbar * spinKroneckerDelta row.1 column.1 *
          pauliForAxis axis row.2.1 column.2.1 *
          spinKroneckerDelta row.2.2 column.2.2
    | .three =>
        halfHbar * spinKroneckerDelta row.1 column.1 *
          spinKroneckerDelta row.2.1 column.2.1 *
          pauliForAxis axis row.2.2 column.2.2

/-- The pair interaction `S_first · S_second`, summed over `x`, `y`, and `z`. -/
def pairSpinDotMatrix
    (first second : TriangleSite) : Matrix ThreeSpinBasis ThreeSpinBasis ℂ :=
  ∑ axis : SpinAxis,
    localSpinComponentMatrix first axis * localSpinComponentMatrix second axis

/--
The matrix `J (S₁·S₂ + S₂·S₃ + S₃·S₁)` for the complete triangular bond
graph.  The scalar parameter is the positive antiferromagnetic exchange
coupling.
-/
def triangularHeisenbergHamiltonianMatrix
    (exchangeCouplingJoulesPerActionSquared : ℝ) :
    Matrix ThreeSpinBasis ThreeSpinBasis ℂ :=
  (exchangeCouplingJoulesPerActionSquared : ℂ) •
    (pairSpinDotMatrix .one .two +
      pairSpinDotMatrix .two .three +
      pairSpinDotMatrix .three .one)

/-- The matrix Hamiltonian interpreted as an endomorphism of the Hilbert space. -/
def triangularHeisenbergHamiltonian
    (exchangeCouplingJoulesPerActionSquared : ℝ) :
    Module.End ℂ ThreeSpinState :=
  Matrix.toLin threeSpinBasis threeSpinBasis
    (triangularHeisenbergHamiltonianMatrix
      exchangeCouplingJoulesPerActionSquared)

/-! ## Experiment and governing assumptions -/

/--
The independent physical data of the experiment.  The Hamiltonian remains an
operator on the three-spin Hilbert space until the governing-law premise below
identifies its matrix.
-/
structure SpinHalfTriangleExperiment where
  exchangeCouplingJoulesPerActionSquared : ℝ
  hamiltonian : Module.End ℂ ThreeSpinState
  figure : SpinTriangleFigure

/-- Positive exchange selects the antiferromagnetic regime stated in the source. -/
structure HasAntiferromagneticExchange
    (experiment : SpinHalfTriangleExperiment) : Prop where
  positiveExchangeCoupling :
    0 < experiment.exchangeCouplingJoulesPerActionSquared

/--
The stated Heisenberg governing law.  This premise fixes the operator from the
local spin-`1/2` matrices but contains no ground-energy or degeneracy claim.
-/
structure SatisfiesTriangularHeisenbergHamiltonian
    (experiment : SpinHalfTriangleExperiment) : Prop where
  hamiltonianIsPairwiseSpinDotSum :
    experiment.hamiltonian =
      triangularHeisenbergHamiltonian
        experiment.exchangeCouplingJoulesPerActionSquared

/-! ## Spectral vocabulary and displayed choices -/

/-- A real energy readout whose complex coercion is an eigenvalue of `H`. -/
def HasEnergyEigenvalue
    (hamiltonian : Module.End ℂ ThreeSpinState)
    (energyJoules : ℝ) : Prop :=
  hamiltonian.HasEigenvalue (energyJoules : ℂ)

/--
`energyJoules` is an eigenvalue and is no larger than any other real energy
eigenvalue of the Hamiltonian.
-/
def IsGroundStateEnergy
    (hamiltonian : Module.End ℂ ThreeSpinState)
    (energyJoules : ℝ) : Prop :=
  HasEnergyEigenvalue hamiltonian energyJoules ∧
    ∀ otherEnergyJoules : ℝ,
      HasEnergyEigenvalue hamiltonian otherEnergyJoules →
        energyJoules ≤ otherEnergyJoules

/-- The degeneracy of an energy is the complex dimension of its eigenspace. -/
def energyLevelDegeneracy
    (hamiltonian : Module.End ℂ ThreeSpinState)
    (energyJoules : ℝ) : ℕ :=
  Module.finrank ℂ (hamiltonian.eigenspace (energyJoules : ℂ))

/-- Labels of the four energy expressions displayed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed energy readouts, with their common dimensional scale. -/
def displayedEnergyJoules
    (choice : AnswerChoice)
    (exchangeCouplingJoulesPerActionSquared : ℝ) : ℝ :=
  match choice with
  | .A =>
      -(9 / 4 : ℝ) * exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2
  | .B => 0
  | .C =>
      -(3 / 4 : ℝ) * exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2
  | .D =>
      (3 / 4 : ℝ) * exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2

/-!
Blueprint: `thm:physics:phyx_mini_0606:target`.

For positive exchange, the frustrated spin triangle has ground-state energy
`-(3/4) J ℏ²`.  Its ground eigenspace has complex dimension four (two spin
doublets), and the energy is the expression displayed as choice C.
-/
theorem groundStateEnergyAndDegeneracy
    (experiment : SpinHalfTriangleExperiment)
    (hFigure : MatchesSuppliedSpinTriangleFigure experiment.figure)
    (hAntiferromagnetic : HasAntiferromagneticExchange experiment)
    (hHamiltonian : SatisfiesTriangularHeisenbergHamiltonian experiment) :
    let groundEnergyJoules : ℝ :=
      -(3 / 4 : ℝ) *
        experiment.exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2
    IsGroundStateEnergy experiment.hamiltonian groundEnergyJoules ∧
      energyLevelDegeneracy experiment.hamiltonian groundEnergyJoules = 4 ∧
      displayedEnergyJoules .C
          experiment.exchangeCouplingJoulesPerActionSquared =
        groundEnergyJoules := by
  dsimp
  exact finishSpectrum experiment
    (triangularHeisenbergHamiltonian
      experiment.exchangeCouplingJoulesPerActionSquared)
    (fun i => (i.2.1, (i.1, i.2.2)))
    (fun i => (i.1, (i.2.2, i.2.1)))
    (fun i => (i.2.2, (i.2.1, i.1)))
    ((experiment.exchangeCouplingJoulesPerActionSquared : ℂ) *
      (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))
    hHamiltonian.hamiltonianIsPairwiseSpinDotSum
    (heisenbergAction experiment.exchangeCouplingJoulesPerActionSquared)
    (by intro i; rfl) (by intro i; rfl) (by intro i; rfl) rfl
    hAntiferromagnetic.positiveExchangeCoupling
where
  pauliCompleteness (a b i j : Fin 2) :
      (∑ axis : SpinAxis,
          pauliForAxis axis a i * pauliForAxis axis b j) =
        2 * spinKroneckerDelta a j * spinKroneckerDelta b i -
          spinKroneckerDelta a i * spinKroneckerDelta b j := by
    have hSpinAxisUniv :
        (Finset.univ : Finset SpinAxis) = {.x, .y, .z} := by
      decide
    let flipSpin : Fin 2 → Fin 2
      | 0 => 1
      | 1 => 0
    let yPhase : Fin 2 → ℂ
      | 0 => Complex.I
      | 1 => -Complex.I
    let zPhase : Fin 2 → ℂ
      | 0 => 1
      | 1 => -1
    rw [show
        (∑ axis : SpinAxis,
            pauliForAxis axis a i * pauliForAxis axis b j) =
          pauliForAxis .x a i * pauliForAxis .x b j +
            pauliForAxis .y a i * pauliForAxis .y b j +
            pauliForAxis .z a i * pauliForAxis .z b j by
          rw [hSpinAxisUniv]
          simp
          ring]
    rw [show pauliForAxis .x a i =
            spinKroneckerDelta a (flipSpin i) by
          fin_cases a <;> fin_cases i <;> rfl,
        show pauliForAxis .x b j =
            spinKroneckerDelta b (flipSpin j) by
          fin_cases b <;> fin_cases j <;> rfl,
        show pauliForAxis .y a i =
            yPhase i * spinKroneckerDelta a (flipSpin i) by
          fin_cases a <;> fin_cases i <;>
            simp [pauliForAxis, SpinAxis.toFin3,
              PauliMatrix.pauliMatrix, yPhase, flipSpin,
              spinKroneckerDelta],
        show pauliForAxis .y b j =
            yPhase j * spinKroneckerDelta b (flipSpin j) by
          fin_cases b <;> fin_cases j <;>
            simp [pauliForAxis, SpinAxis.toFin3,
              PauliMatrix.pauliMatrix, yPhase, flipSpin,
              spinKroneckerDelta],
        show pauliForAxis .z a i =
            zPhase i * spinKroneckerDelta a i by
          fin_cases a <;> fin_cases i <;>
            simp [pauliForAxis, SpinAxis.toFin3,
              PauliMatrix.pauliMatrix, zPhase, spinKroneckerDelta],
        show pauliForAxis .z b j =
            zPhase j * spinKroneckerDelta b j by
          fin_cases b <;> fin_cases j <;>
            simp [pauliForAxis, SpinAxis.toFin3,
              PauliMatrix.pauliMatrix, zPhase, spinKroneckerDelta]]
    fin_cases i <;> fin_cases j <;>
      simp only [flipSpin, yPhase, zPhase]
    all_goals ring_nf
    all_goals simp [Complex.I_sq]
    all_goals ring

  normalizedMatrixIdentity
      (normalized : TriangleSite → SpinAxis →
        Matrix ThreeSpinBasis ThreeSpinBasis ℂ)
      (swapOneTwo swapTwoThree swapThreeOne :
        ThreeSpinBasis → ThreeSpinBasis)
      (hNormalized : ∀ site axis row column,
        normalized site axis row column =
          match site with
          | .one =>
              pauliForAxis axis row.1 column.1 *
                spinKroneckerDelta row.2.1 column.2.1 *
                spinKroneckerDelta row.2.2 column.2.2
          | .two =>
              spinKroneckerDelta row.1 column.1 *
                pauliForAxis axis row.2.1 column.2.1 *
                spinKroneckerDelta row.2.2 column.2.2
          | .three =>
              spinKroneckerDelta row.1 column.1 *
                spinKroneckerDelta row.2.1 column.2.1 *
                pauliForAxis axis row.2.2 column.2.2)
      (hSwapOneTwo : ∀ i, swapOneTwo i = (i.2.1, (i.1, i.2.2)))
      (hSwapTwoThree : ∀ i, swapTwoThree i = (i.1, (i.2.2, i.2.1)))
      (hSwapThreeOne : ∀ i, swapThreeOne i = (i.2.2, (i.2.1, i.1))) :
      (∑ axis : SpinAxis, normalized .one axis * normalized .two axis) +
          (∑ axis : SpinAxis, normalized .two axis * normalized .three axis) +
        (∑ axis : SpinAxis, normalized .three axis * normalized .one axis) =
      fun row column =>
        2 * ((if row = swapOneTwo column then 1 else 0) +
          (if row = swapTwoThree column then 1 else 0) +
          (if row = swapThreeOne column then 1 else 0)) -
          3 * (if row = column then 1 else 0) := by
    have hDoubleIteComm
        (p q : Prop) [Decidable p] [Decidable q] (x : ℂ) :
        (if p then if q then x else 0 else 0) =
          if q then if p then x else 0 else 0 := by
      by_cases hp : p <;> simp [hp]
    have hPairOneTwo :
        (∑ axis : SpinAxis, normalized .one axis * normalized .two axis) =
          fun row column =>
            2 * (if row = swapOneTwo column then 1 else 0) -
              (if row = column then 1 else 0) := by
      ext ⟨a, b, c⟩ ⟨i, j, k⟩
      change
        (∑ axis : SpinAxis,
            (normalized .one axis * normalized .two axis)
              (a, (b, c)) (i, (j, k))) = _
      rw [show
          (fun axis : SpinAxis =>
              (normalized .one axis * normalized .two axis)
                (a, (b, c)) (i, (j, k))) =
            fun axis => ∑ x : ThreeSpinBasis,
              normalized .one axis (a, (b, c)) x *
                normalized .two axis x (i, (j, k)) by
            funext axis
            rw [Matrix.mul_apply]]
      simp [hNormalized, Fintype.sum_prod_type, spinKroneckerDelta,
        pauliCompleteness, hSwapOneTwo]
      by_cases hck : c = k
      · simp only [hck, ↓reduceIte, and_true]
        simp only [ite_and]
        rw [hDoubleIteComm (b = i) (a = j) 2,
          hDoubleIteComm (b = j) (a = i) 1]
      · simp [hck]
    have hPairTwoThree :
        (∑ axis : SpinAxis, normalized .two axis * normalized .three axis) =
          fun row column =>
            2 * (if row = swapTwoThree column then 1 else 0) -
              (if row = column then 1 else 0) := by
      ext ⟨a, b, c⟩ ⟨i, j, k⟩
      change
        (∑ axis : SpinAxis,
            (normalized .two axis * normalized .three axis)
              (a, (b, c)) (i, (j, k))) = _
      rw [show
          (fun axis : SpinAxis =>
              (normalized .two axis * normalized .three axis)
                (a, (b, c)) (i, (j, k))) =
            fun axis => ∑ x : ThreeSpinBasis,
              normalized .two axis (a, (b, c)) x *
                normalized .three axis x (i, (j, k)) by
            funext axis
            rw [Matrix.mul_apply]]
      simp [hNormalized, Fintype.sum_prod_type, spinKroneckerDelta,
        pauliCompleteness, hSwapTwoThree]
      by_cases hai : a = i
      · simp only [hai, ↓reduceIte, true_and]
        simp only [ite_and]
        rw [hDoubleIteComm (c = j) (b = k) 2,
          hDoubleIteComm (c = k) (b = j) 1]
      · simp [hai]
    have hPairThreeOne :
        (∑ axis : SpinAxis, normalized .three axis * normalized .one axis) =
          fun row column =>
            2 * (if row = swapThreeOne column then 1 else 0) -
              (if row = column then 1 else 0) := by
      ext ⟨a, b, c⟩ ⟨i, j, k⟩
      change
        (∑ axis : SpinAxis,
            (normalized .three axis * normalized .one axis)
              (a, (b, c)) (i, (j, k))) = _
      rw [show
          (fun axis : SpinAxis =>
              (normalized .three axis * normalized .one axis)
                (a, (b, c)) (i, (j, k))) =
            fun axis => ∑ x : ThreeSpinBasis,
              normalized .three axis (a, (b, c)) x *
                normalized .one axis x (i, (j, k)) by
            funext axis
            rw [Matrix.mul_apply]]
      simp [hNormalized, Fintype.sum_prod_type, spinKroneckerDelta,
        pauliCompleteness, hSwapThreeOne]
      by_cases hbj : b = j
      · simp only [hbj, ↓reduceIte]
        simp only [ite_and]
        simp
      · simp [hbj]
    rw [hPairOneTwo, hPairTwoThree, hPairThreeOne]
    ext row column
    simp
    split_ifs <;> ring

  matrixOnBasis_of_entry_formula
      (matrix : Matrix ThreeSpinBasis ThreeSpinBasis ℂ)
      (swapOneTwo swapTwoThree swapThreeOne :
        ThreeSpinBasis → ThreeSpinBasis)
      (energyScale : ℂ)
      (hEntry : ∀ row column,
        matrix row column =
          (if row = swapOneTwo column then 2 * energyScale else 0) +
            (if row = swapTwoThree column then 2 * energyScale else 0) +
            (if row = swapThreeOne column then 2 * energyScale else 0) -
            (if row = column then 3 * energyScale else 0)) :
      ∀ i,
        Matrix.toLin threeSpinBasis threeSpinBasis matrix (threeSpinBasis i) =
          (2 * energyScale) • threeSpinBasis (swapOneTwo i) +
            (2 * energyScale) • threeSpinBasis (swapTwoThree i) +
            (2 * energyScale) • threeSpinBasis (swapThreeOne i) -
            (3 * energyScale) • threeSpinBasis i := by
    intro i
    rw [Matrix.toLin_self]
    simp [hEntry, add_smul, sub_smul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp

  heisenbergAction (exchangeCouplingJoulesPerActionSquared : ℝ) :
      ∀ i : ThreeSpinBasis,
        triangularHeisenbergHamiltonian
            exchangeCouplingJoulesPerActionSquared (threeSpinBasis i) =
          (2 * ((exchangeCouplingJoulesPerActionSquared : ℂ) *
              (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))) •
              threeSpinBasis (i.2.1, (i.1, i.2.2)) +
            (2 * ((exchangeCouplingJoulesPerActionSquared : ℂ) *
              (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))) •
              threeSpinBasis (i.1, (i.2.2, i.2.1)) +
            (2 * ((exchangeCouplingJoulesPerActionSquared : ℂ) *
              (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))) •
              threeSpinBasis (i.2.2, (i.2.1, i.1)) -
            (3 * ((exchangeCouplingJoulesPerActionSquared : ℂ) *
              (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))) • threeSpinBasis i := by
    have hScaleIndicator
        (p : Prop) [Decidable p] (x : ℂ) :
        (if p then x else 0) = x * (if p then 1 else 0) := by
      by_cases hp : p <;> simp [hp]
    let swapOneTwo : ThreeSpinBasis → ThreeSpinBasis := fun i =>
      (i.2.1, (i.1, i.2.2))
    let swapTwoThree : ThreeSpinBasis → ThreeSpinBasis := fun i =>
      (i.1, (i.2.2, i.2.1))
    let swapThreeOne : ThreeSpinBasis → ThreeSpinBasis := fun i =>
      (i.2.2, (i.2.1, i.1))
    let normalized
        (site : TriangleSite) (axis : SpinAxis) :
        Matrix ThreeSpinBasis ThreeSpinBasis ℂ :=
      fun row column =>
        match site with
        | .one =>
            pauliForAxis axis row.1 column.1 *
              spinKroneckerDelta row.2.1 column.2.1 *
              spinKroneckerDelta row.2.2 column.2.2
        | .two =>
            spinKroneckerDelta row.1 column.1 *
              pauliForAxis axis row.2.1 column.2.1 *
              spinKroneckerDelta row.2.2 column.2.2
        | .three =>
            spinKroneckerDelta row.1 column.1 *
              spinKroneckerDelta row.2.1 column.2.1 *
              pauliForAxis axis row.2.2 column.2.2
    let halfHbar : ℂ := (((Constants.ℏ : ℝ) / 2 : ℝ) : ℂ)
    have hLocalSpinComponentMatrix (site : TriangleSite) (axis : SpinAxis) :
        localSpinComponentMatrix site axis =
          halfHbar • normalized site axis := by
      ext row column
      rcases site <;>
        simp [localSpinComponentMatrix, normalized, halfHbar] <;>
        ring
    have hPairSpinDotMatrix (first second : TriangleSite) :
        pairSpinDotMatrix first second =
          halfHbar ^ 2 •
            ∑ axis : SpinAxis, normalized first axis * normalized second axis := by
      rw [pairSpinDotMatrix]
      simp [hLocalSpinComponentMatrix, smul_smul, Finset.smul_sum, pow_two]
    have hNormalizedMatrix :
        (∑ axis : SpinAxis, normalized .one axis * normalized .two axis) +
            (∑ axis : SpinAxis, normalized .two axis * normalized .three axis) +
          (∑ axis : SpinAxis, normalized .three axis * normalized .one axis) =
        fun row column =>
          2 * ((if row = swapOneTwo column then 1 else 0) +
            (if row = swapTwoThree column then 1 else 0) +
            (if row = swapThreeOne column then 1 else 0)) -
            3 * (if row = column then 1 else 0) := by
      exact normalizedMatrixIdentity normalized swapOneTwo swapTwoThree
        swapThreeOne (by intro site axis row column; rfl)
        (by intro i; rfl) (by intro i; rfl) (by intro i; rfl)
    let reducedMatrix : Matrix ThreeSpinBasis ThreeSpinBasis ℂ :=
      fun row column =>
        (exchangeCouplingJoulesPerActionSquared : ℂ) *
          (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4) *
          (2 * ((if row = swapOneTwo column then 1 else 0) +
            (if row = swapTwoThree column then 1 else 0) +
            (if row = swapThreeOne column then 1 else 0)) -
            3 * (if row = column then 1 else 0))
    have hReducedMatrix :
        triangularHeisenbergHamiltonianMatrix
            exchangeCouplingJoulesPerActionSquared = reducedMatrix := by
      rw [triangularHeisenbergHamiltonianMatrix, hPairSpinDotMatrix,
        hPairSpinDotMatrix, hPairSpinDotMatrix]
      rw [← smul_add, ← smul_add, hNormalizedMatrix]
      ext row column
      simp [reducedMatrix, halfHbar]
      ring
    have hReducedHamiltonian :
        triangularHeisenbergHamiltonian
            exchangeCouplingJoulesPerActionSquared =
          Matrix.toLin threeSpinBasis threeSpinBasis reducedMatrix := by
      simp [triangularHeisenbergHamiltonian, hReducedMatrix]
    let energyScale : ℂ :=
      (exchangeCouplingJoulesPerActionSquared : ℂ) *
        (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4)
    have hReducedMatrixEntry (row column : ThreeSpinBasis) :
        reducedMatrix row column =
          (if row = swapOneTwo column then 2 * energyScale else 0) +
            (if row = swapTwoThree column then 2 * energyScale else 0) +
            (if row = swapThreeOne column then 2 * energyScale else 0) -
            (if row = column then 3 * energyScale else 0) := by
      rw [hScaleIndicator (row = swapOneTwo column) (2 * energyScale),
        hScaleIndicator (row = swapTwoThree column) (2 * energyScale),
        hScaleIndicator (row = swapThreeOne column) (2 * energyScale),
        hScaleIndicator (row = column) (3 * energyScale)]
      simp only [reducedMatrix, energyScale]
      ring
    intro i
    rw [hReducedHamiltonian]
    exact matrixOnBasis_of_entry_formula reducedMatrix swapOneTwo swapTwoThree
      swapThreeOne energyScale hReducedMatrixEntry i

  spectralVector_eigen
      (e : ThreeSpinBasis → ThreeSpinState)
      (T : Module.End ℂ ThreeSpinState)
      (swapOneTwo swapTwoThree swapThreeOne :
        ThreeSpinBasis → ThreeSpinBasis)
      (energyScale groundEnergy excitedEnergy : ℂ)
      (hOnBasis : ∀ i,
        T (e i) =
          (2 * energyScale) • e (swapOneTwo i) +
            (2 * energyScale) • e (swapTwoThree i) +
            (2 * energyScale) • e (swapThreeOne i) -
            (3 * energyScale) • e i)
      (hSwapOneTwo :
        swapOneTwo = fun i => (i.2.1, (i.1, i.2.2)))
      (hSwapTwoThree :
        swapTwoThree = fun i => (i.1, (i.2.2, i.2.1)))
      (hSwapThreeOne :
        swapThreeOne = fun i => (i.2.2, (i.2.1, i.1)))
      (hGroundEnergy : groundEnergy = -3 * energyScale)
      (hExcitedEnergy : excitedEnergy = 3 * energyScale) :
      let eigenvector : ThreeSpinBasis → ThreeSpinState := fun i =>
        if i.1 = 0 then
          if i.2.1 = 0 then
            if i.2.2 = 0 then e (0, (0, 1)) - e (0, (1, 0))
            else e (0, (0, 1)) - e (1, (0, 0))
          else
            if i.2.2 = 0 then e (1, (1, 0)) - e (1, (0, 1))
            else e (1, (1, 0)) - e (0, (1, 1))
        else
          if i.2.1 = 0 then
            if i.2.2 = 0 then e (0, (0, 0))
            else e (1, (1, 1))
          else
            if i.2.2 = 0 then
              e (0, (0, 1)) + e (0, (1, 0)) + e (1, (0, 0))
            else
              e (1, (1, 0)) + e (1, (0, 1)) + e (0, (1, 1))
      ∀ i, T (eigenvector i) =
        (if i.1 = 0 then groundEnergy else excitedEnergy) • eigenvector i := by
    dsimp only
    intro i
    have hFinTwoCases (x : Fin 2) : x = 0 ∨ x = 1 := by
      omega
    rcases i with ⟨i, j, k⟩
    rcases hFinTwoCases i with rfl | rfl <;>
      rcases hFinTwoCases j with rfl | rfl <;>
      rcases hFinTwoCases k with rfl | rfl
    all_goals simp
    all_goals repeat' rw [hOnBasis]
    all_goals simp [hSwapOneTwo, hSwapTwoThree, hSwapThreeOne,
      hGroundEnergy, hExcitedEnergy]
    all_goals module

  groundEigenspace_diagonal
      (eigenBasis : Module.Basis ThreeSpinBasis ℂ ThreeSpinState)
      (eigenvalue : ThreeSpinBasis → ℂ)
      (groundEnergy excitedEnergy : ℂ)
      (hEigenvalue : ∀ i,
        eigenvalue i = if i.1 = 0 then groundEnergy else excitedEnergy)
      (hEnergyNe : excitedEnergy ≠ groundEnergy) :
      Module.End.eigenspace
          (Matrix.toLin eigenBasis eigenBasis
            (Matrix.diagonal eigenvalue) : Module.End ℂ ThreeSpinState)
          groundEnergy =
        Submodule.span ℂ
          (Set.range (fun i : {i : ThreeSpinBasis // i.1 = 0} =>
            eigenBasis i.1)) := by
    have hDiagonalCoordinate (x : ThreeSpinState) (i : ThreeSpinBasis) :
        eigenBasis.repr
            ((Matrix.toLin eigenBasis eigenBasis
              (Matrix.diagonal eigenvalue) : Module.End ℂ ThreeSpinState) x) i =
          eigenvalue i * eigenBasis.repr x i := by
      classical
      rw [Matrix.toLin_apply]
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Finsupp.single_apply]
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      rw [← eigenBasis.sum_repr x]
      apply Submodule.sum_mem
      intro i hi
      by_cases hiZero : i.1 = 0
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨i, hiZero⟩, rfl⟩
      · have hCoordinate :=
          congrArg (fun y => eigenBasis.repr y i) hx
        rw [hDiagonalCoordinate] at hCoordinate
        simp [hEigenvalue, hiZero] at hCoordinate
        have hCoefficientZero : eigenBasis.repr x i = 0 :=
          hCoordinate.resolve_left hEnergyNe
        rw [hCoefficientZero, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Module.End.mem_eigenspace_iff.mpr (by
        rw [Matrix.toLin_self]
        simp [Matrix.diagonal, hEigenvalue, i.2])

  spectralVector_linearIndependent :
      LinearIndependent ℂ (fun i : ThreeSpinBasis =>
        if i.1 = 0 then
          if i.2.1 = 0 then
            if i.2.2 = 0 then
              threeSpinBasis (0, (0, 1)) - threeSpinBasis (0, (1, 0))
            else
              threeSpinBasis (0, (0, 1)) - threeSpinBasis (1, (0, 0))
          else
            if i.2.2 = 0 then
              threeSpinBasis (1, (1, 0)) - threeSpinBasis (1, (0, 1))
            else
              threeSpinBasis (1, (1, 0)) - threeSpinBasis (0, (1, 1))
        else
          if i.2.1 = 0 then
            if i.2.2 = 0 then threeSpinBasis (0, (0, 0))
            else threeSpinBasis (1, (1, 1))
          else
            if i.2.2 = 0 then
              threeSpinBasis (0, (0, 1)) +
                  threeSpinBasis (0, (1, 0)) +
                threeSpinBasis (1, (0, 0))
            else
              threeSpinBasis (1, (1, 0)) +
                  threeSpinBasis (1, (0, 1)) +
                threeSpinBasis (0, (1, 1))) := by
    apply LinearIndependent.of_comp threeSpinBasis.repr.toLinearMap
    rw [Fintype.linearIndependent_iff]
    intro coefficients hsum i
    have hCoordinate (j : ThreeSpinBasis) :=
      congrArg (fun x => x j) hsum
    have h000 := hCoordinate (0, (0, 0))
    have h001 := hCoordinate (0, (0, 1))
    have h010 := hCoordinate (0, (1, 0))
    have h011 := hCoordinate (0, (1, 1))
    have h100 := hCoordinate (1, (0, 0))
    have h101 := hCoordinate (1, (0, 1))
    have h110 := hCoordinate (1, (1, 0))
    have h111 := hCoordinate (1, (1, 1))
    simp [Fintype.sum_prod_type, Fin.sum_univ_two] at h000 h001 h010 h011 h100 h101 h110 h111
    have h000' : coefficients (0, (0, 0)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h001 - (2 / 3 : ℂ) * h010 +
        (1 / 3 : ℂ) * h100
    have h001' : coefficients (0, (0, 1)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h001 + (1 / 3 : ℂ) * h010 -
        (2 / 3 : ℂ) * h100
    have h110' : coefficients (1, (1, 0)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h001 + (1 / 3 : ℂ) * h010 +
        (1 / 3 : ℂ) * h100
    have h010' : coefficients (0, (1, 0)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h110 - (2 / 3 : ℂ) * h101 +
        (1 / 3 : ℂ) * h011
    have h011' : coefficients (0, (1, 1)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h110 + (1 / 3 : ℂ) * h101 -
        (2 / 3 : ℂ) * h011
    have h111' : coefficients (1, (1, 1)) = 0 := by
      linear_combination (1 / 3 : ℂ) * h110 + (1 / 3 : ℂ) * h101 +
        (1 / 3 : ℂ) * h011
    rcases i with ⟨i, j, k⟩
    fin_cases i <;> fin_cases j <;> fin_cases k
    · exact h000'
    · exact h001'
    · exact h010'
    · exact h011'
    · exact h000
    · exact h111
    · exact h110'
    · exact h111'

  finishSpectrum
      (experiment : SpinHalfTriangleExperiment)
      (T : Module.End ℂ ThreeSpinState)
      (swapOneTwo swapTwoThree swapThreeOne :
        ThreeSpinBasis → ThreeSpinBasis)
      (energyScale : ℂ)
      (hExperimentT : experiment.hamiltonian = T)
      (hOnBasis : ∀ i,
        T (threeSpinBasis i) =
          (2 * energyScale) • threeSpinBasis (swapOneTwo i) +
            (2 * energyScale) • threeSpinBasis (swapTwoThree i) +
            (2 * energyScale) • threeSpinBasis (swapThreeOne i) -
            (3 * energyScale) • threeSpinBasis i)
      (hSwapOneTwo :
        ∀ i, swapOneTwo i = (i.2.1, (i.1, i.2.2)))
      (hSwapTwoThree :
        ∀ i, swapTwoThree i = (i.1, (i.2.2, i.2.1)))
      (hSwapThreeOne :
        ∀ i, swapThreeOne i = (i.2.2, (i.2.1, i.1)))
      (hEnergyScale :
        energyScale =
          (experiment.exchangeCouplingJoulesPerActionSquared : ℂ) *
            (((Constants.ℏ : ℝ) : ℂ) ^ 2 / 4))
      (hPositive : 0 < experiment.exchangeCouplingJoulesPerActionSquared) :
      let groundEnergyJoules : ℝ :=
        -(3 / 4 : ℝ) *
          experiment.exchangeCouplingJoulesPerActionSquared *
          (Constants.ℏ : ℝ) ^ 2
      IsGroundStateEnergy experiment.hamiltonian groundEnergyJoules ∧
        energyLevelDegeneracy experiment.hamiltonian groundEnergyJoules = 4 ∧
        displayedEnergyJoules .C
            experiment.exchangeCouplingJoulesPerActionSquared =
          groundEnergyJoules := by
    dsimp
    let eigenvector : ThreeSpinBasis → ThreeSpinState := fun i =>
      if i.1 = 0 then
        if i.2.1 = 0 then
          if i.2.2 = 0 then
            threeSpinBasis (0, (0, 1)) - threeSpinBasis (0, (1, 0))
          else
            threeSpinBasis (0, (0, 1)) - threeSpinBasis (1, (0, 0))
        else
          if i.2.2 = 0 then
            threeSpinBasis (1, (1, 0)) - threeSpinBasis (1, (0, 1))
          else
            threeSpinBasis (1, (1, 0)) - threeSpinBasis (0, (1, 1))
      else
        if i.2.1 = 0 then
          if i.2.2 = 0 then threeSpinBasis (0, (0, 0))
          else threeSpinBasis (1, (1, 1))
        else
          if i.2.2 = 0 then
            threeSpinBasis (0, (0, 1)) +
                threeSpinBasis (0, (1, 0)) +
              threeSpinBasis (1, (0, 0))
          else
            threeSpinBasis (1, (1, 0)) +
                threeSpinBasis (1, (0, 1)) +
              threeSpinBasis (0, (1, 1))
    have hEigenvectorLinearIndependent : LinearIndependent ℂ eigenvector := by
      exact spectralVector_linearIndependent
    let groundEnergyReal : ℝ :=
      -(3 / 4 : ℝ) *
        experiment.exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2
    let excitedEnergyReal : ℝ :=
      (3 / 4 : ℝ) *
        experiment.exchangeCouplingJoulesPerActionSquared *
        (Constants.ℏ : ℝ) ^ 2
    let groundEnergy : ℂ := groundEnergyReal
    let excitedEnergy : ℂ := excitedEnergyReal
    let eigenvalue : ThreeSpinBasis → ℂ := fun i =>
      if i.1 = 0 then groundEnergy else excitedEnergy
    have hGroundEnergyScale : groundEnergy = -3 * energyScale := by
      dsimp [groundEnergy, groundEnergyReal]
      rw [hEnergyScale]
      push_cast
      ring
    have hExcitedEnergyScale : excitedEnergy = 3 * energyScale := by
      dsimp [excitedEnergy, excitedEnergyReal]
      rw [hEnergyScale]
      push_cast
      ring
    have hEigenvector (i : ThreeSpinBasis) :
        T (eigenvector i) = eigenvalue i • eigenvector i := by
      exact spectralVector_eigen threeSpinBasis T swapOneTwo swapTwoThree
        swapThreeOne energyScale groundEnergy excitedEnergy hOnBasis
        (funext hSwapOneTwo) (funext hSwapTwoThree) (funext hSwapThreeOne)
        hGroundEnergyScale hExcitedEnergyScale i
    let eigenBasis : Module.Basis ThreeSpinBasis ℂ ThreeSpinState :=
      basisOfLinearIndependentOfCardEqFinrank
        hEigenvectorLinearIndependent
        (Module.finrank_eq_card_basis threeSpinBasis).symm
    have hEigenBasis (i : ThreeSpinBasis) :
        eigenBasis i = eigenvector i := by
      simp [eigenBasis]
    have hDiagonal :
        T = Matrix.toLin eigenBasis eigenBasis (Matrix.diagonal eigenvalue) := by
      apply eigenBasis.ext
      intro i
      rw [Matrix.toLin_self]
      simp [hEigenBasis, hEigenvector, Matrix.diagonal]
    have hExperimentDiagonal :
        experiment.hamiltonian =
          Matrix.toLin eigenBasis eigenBasis (Matrix.diagonal eigenvalue) :=
      hExperimentT.trans hDiagonal
    have hGroundEigenvalue :
        HasEnergyEigenvalue experiment.hamiltonian groundEnergyReal := by
      rw [HasEnergyEigenvalue, hExperimentDiagonal,
        hasEigenvalue_toLin_diagonal_iff eigenvalue eigenBasis]
      exact ⟨(0, (0, 0)), by simp [eigenvalue, groundEnergy]⟩
    have hGroundOrder :
        ∀ otherEnergyJoules : ℝ,
          HasEnergyEigenvalue experiment.hamiltonian otherEnergyJoules →
            groundEnergyReal ≤ otherEnergyJoules := by
      intro otherEnergyJoules hOther
      rw [HasEnergyEigenvalue, hExperimentDiagonal,
        hasEigenvalue_toLin_diagonal_iff eigenvalue eigenBasis] at hOther
      obtain ⟨i, hi⟩ := hOther
      by_cases hiZero : i.1 = 0
      · have hiReal : groundEnergyReal = otherEnergyJoules := by
          apply Complex.ofReal_injective
          simpa [eigenvalue, groundEnergy, excitedEnergy, hiZero] using hi
        exact hiReal.le
      · have hiReal : excitedEnergyReal = otherEnergyJoules := by
          apply Complex.ofReal_injective
          simpa [eigenvalue, groundEnergy, excitedEnergy, hiZero] using hi
        rw [← hiReal]
        dsimp [groundEnergyReal, excitedEnergyReal]
        have hScale :
            0 <
              experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 :=
          mul_pos hPositive (pow_pos Constants.ℏ_pos 2)
        have hNonnegative :
            0 ≤
              (3 / 4 : ℝ) *
                (experiment.exchangeCouplingJoulesPerActionSquared *
                  (Constants.ℏ : ℝ) ^ 2) :=
          mul_nonneg (by norm_num) hScale.le
        calc
          -(3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 =
              -((3 / 4 : ℝ) *
                (experiment.exchangeCouplingJoulesPerActionSquared *
                  (Constants.ℏ : ℝ) ^ 2)) := by
            rw [neg_mul, neg_mul]
            simp only [mul_assoc]
          _ ≤
              (3 / 4 : ℝ) *
                (experiment.exchangeCouplingJoulesPerActionSquared *
                  (Constants.ℏ : ℝ) ^ 2) :=
            neg_le_self hNonnegative
          _ =
              (3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 := by
            rw [mul_assoc]
    have hEnergyNe : excitedEnergy ≠ groundEnergy := by
      intro hEqual
      have hEqualReal : excitedEnergyReal = groundEnergyReal := by
        apply Complex.ofReal_injective
        simpa [excitedEnergy, groundEnergy] using hEqual
      have hScale :
          0 <
            experiment.exchangeCouplingJoulesPerActionSquared *
              (Constants.ℏ : ℝ) ^ 2 :=
        mul_pos hPositive (pow_pos Constants.ℏ_pos 2)
      dsimp [excitedEnergyReal, groundEnergyReal] at hEqualReal
      have hPositiveScale :
          0 <
            (3 / 4 : ℝ) *
              (experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2) :=
        mul_pos (by norm_num) hScale
      have hStrict :
          -(3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 <
              (3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 := by
        calc
          -(3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 =
              -((3 / 4 : ℝ) *
                (experiment.exchangeCouplingJoulesPerActionSquared *
                  (Constants.ℏ : ℝ) ^ 2)) := by
            rw [neg_mul, neg_mul]
            simp only [mul_assoc]
          _ <
              (3 / 4 : ℝ) *
                (experiment.exchangeCouplingJoulesPerActionSquared *
                  (Constants.ℏ : ℝ) ^ 2) :=
            neg_lt_self hPositiveScale
          _ =
              (3 / 4 : ℝ) *
                experiment.exchangeCouplingJoulesPerActionSquared *
                (Constants.ℏ : ℝ) ^ 2 := by
            rw [mul_assoc]
      exact (ne_of_lt hStrict) hEqualReal.symm
    let GroundIndex := {i : ThreeSpinBasis // i.1 = 0}
    let groundEigenvector : GroundIndex → ThreeSpinState := fun i =>
      eigenBasis i.1
    have hGroundLinearIndependent :
        LinearIndependent ℂ groundEigenvector := by
      exact eigenBasis.linearIndependent.comp
        (fun i : GroundIndex => i.1) Subtype.val_injective
    have hGroundEigenspace :
        Module.End.eigenspace
            (Matrix.toLin eigenBasis eigenBasis
              (Matrix.diagonal eigenvalue) : Module.End ℂ ThreeSpinState)
            groundEnergy =
          Submodule.span ℂ (Set.range groundEigenvector) := by
      exact groundEigenspace_diagonal eigenBasis eigenvalue groundEnergy
        excitedEnergy (by intro i; rfl) hEnergyNe
    have hDegeneracy :
        energyLevelDegeneracy experiment.hamiltonian groundEnergyReal = 4 := by
      rw [energyLevelDegeneracy, hExperimentDiagonal, hGroundEigenspace,
        finrank_span_eq_card hGroundLinearIndependent]
      exact (by decide)
    refine ⟨⟨hGroundEigenvalue, hGroundOrder⟩, hDegeneracy, ?_⟩
    rfl

end PhyXMiniProblems.ProblemPhyXMini0606
