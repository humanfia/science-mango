import Mathlib
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0545

open Dimension

/-!
# First-order energy shift from a step in an infinite square well

The supplied bitmap shows an unperturbed infinite square well of width `L`
and a resultant well whose added potential is zero on the left half and has
height `V₀` on the right half.  The hard walls are represented by confinement
and boundary conditions, rather than by assigning the real number `∞` to a
potential-energy function.

Length, mass, and energy are unit-independent Physlib quantities.  The real
functions below are explicitly SI coordinate charts: positions are in metres,
potential values are in joules, and wavefunction amplitudes have dimensional
role `m⁻¹ᐟ²`.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Quantum states and figure vocabulary -/

/-- The idealized confinement represented by both potential diagrams. -/
inductive ConfinementModel where
  | oneDimensionalInfiniteSquareWell
  | other
  deriving DecidableEq, Repr

/-- Shape of the finite perturbation inside the hard walls. -/
inductive PerturbationProfile where
  | constantStepOnRightHalf
  | other
  deriving DecidableEq, Repr

/-- The two side-by-side panels in the supplied bitmap. -/
inductive DiagramPanel where
  | originalWell
  | resultantWell
  deriving DecidableEq, Fintype, Repr

/-- Horizontal and vertical axes drawn in each panel. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to a graph axis. -/
inductive AxisQuantity where
  | positionX
  | potentialEnergyVOfX
  deriving DecidableEq, Repr

/-- Symbolic position marks printed along the horizontal axes. -/
inductive FigurePositionMark where
  | leftBoundaryZero
  | midpointLOverTwo
  | rightBoundaryL
  deriving DecidableEq, Fintype, Repr

/-- Other literal labels visible in the two panels. -/
inductive FigureLabel where
  | positionX
  | potentialVOfX
  | infinityAtRightWall
  | stepHeightVZero
  deriving DecidableEq, Repr

/-!
Figure data transcribed from the primary bitmap.  Its coordinate and energy
readouts interpret the symbolic marks `0`, `L/2`, `L`, and `V₀` in the SI
chart; the raster provides no independent numerical calibration.
-/
structure InfiniteSquareWellStepFigure where
  showsPanel : DiagramPanel → Bool
  axisQuantity : DiagramPanel → FigureAxis → AxisQuantity
  showsPositionMark : DiagramPanel → FigurePositionMark → Bool
  showsLabel : DiagramPanel → FigureLabel → Bool
  positionInMeters : FigurePositionMark → ℝ
  stepHeightInJoules : ℝ
  originalInteriorDrawnAtZero : Bool
  resultantLeftHalfDrawnAtZero : Bool
  resultantRightHalfDrawnAtConstantStep : Bool
  stepBeginsAtMidpoint : Bool
  leftBoundaryIsHardWall : DiagramPanel → Bool
  rightBoundaryIsHardWall : DiagramPanel → Bool

/-!
A pointwise representative of unperturbed mode `n`.  `MemHS` records that the
representative lifts to the one-dimensional `L²(ℝ, ℂ)` Hilbert space.
-/
structure InfiniteSquareWellEigenstate (n : ℕ+) where
  unperturbedEnergy : DimEnergy
  amplitudePerSqrtMeter : ℝ → ℂ
  memberOfOneDimensionalHilbertSpace :
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      amplitudePerSqrtMeter

/-!
The particle, width-`L` well, unperturbed modes, finite perturbation, and
response observable.  The first-order corrections are independent fields;
they are constrained only by the general perturbation-theory law below.
-/
structure StepPerturbedInfiniteSquareWellSetup where
  particleMass : MassQuantity
  wellWidth : LengthQuantity
  perturbationStepHeight : DimEnergy
  confinementModel : ConfinementModel
  perturbationProfile : PerturbationProfile
  unperturbedPotentialEnergyInJoules : ℝ → ℝ
  perturbingPotentialEnergyInJoules : ℝ → ℝ
  resultantPotentialEnergyInJoules : ℝ → ℝ
  eigenstate : (n : ℕ+) → InfiniteSquareWellEigenstate n
  firstOrderEnergyCorrection : ℕ+ → DimEnergy
  figure : InfiniteSquareWellStepFigure

/-! ## Scenario, figure readouts, and governing laws -/

/-- Qualitative model stated in the problem. -/
structure MatchesInfiniteSquareWellStepScenario
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  confinementIsInfiniteSquareWell :
    setup.confinementModel = .oneDimensionalInfiniteSquareWell
  perturbationIsRightHalfStep :
    setup.perturbationProfile = .constantStepOnRightHalf

/-!
Exact symbolic and qualitative readouts from the primary bitmap.  In
particular, the image (unlike one sentence of the auxiliary caption) places
the right wall at `L` and the step at `L/2`.
-/
structure MatchesSuppliedPotentialDiagrams
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  bothPanelsAreShown :
    ∀ panel : DiagramPanel, setup.figure.showsPanel panel = true
  horizontalAxesArePosition :
    ∀ panel : DiagramPanel,
      setup.figure.axisQuantity panel .horizontal = .positionX
  verticalAxesArePotentialEnergy :
    ∀ panel : DiagramPanel,
      setup.figure.axisQuantity panel .vertical = .potentialEnergyVOfX
  everyPositionMarkIsShown :
    ∀ panel : DiagramPanel, ∀ mark : FigurePositionMark,
      setup.figure.showsPositionMark panel mark = true
  bothPanelsShowAxisLabels :
    ∀ panel : DiagramPanel,
      setup.figure.showsLabel panel .positionX = true ∧
        setup.figure.showsLabel panel .potentialVOfX = true
  bothPanelsShowInfiniteRightWall :
    ∀ panel : DiagramPanel,
      setup.figure.showsLabel panel .infinityAtRightWall = true
  resultantPanelShowsVZero :
    setup.figure.showsLabel .resultantWell .stepHeightVZero = true
  originalPanelDoesNotShowVZero :
    setup.figure.showsLabel .originalWell .stepHeightVZero = false
  leftMarkIsZero :
    setup.figure.positionInMeters .leftBoundaryZero = 0
  midpointMarkIsHalfWidth :
    setup.figure.positionInMeters .midpointLOverTwo =
      lengthInMeters setup.wellWidth / 2
  rightMarkIsFullWidth :
    setup.figure.positionInMeters .rightBoundaryL =
      lengthInMeters setup.wellWidth
  vZeroLabelNamesStepHeight :
    setup.figure.stepHeightInJoules =
      energyInJoules setup.perturbationStepHeight
  originalInteriorIsZero :
    setup.figure.originalInteriorDrawnAtZero = true
  resultantLeftHalfIsZero :
    setup.figure.resultantLeftHalfDrawnAtZero = true
  resultantRightHalfIsConstant :
    setup.figure.resultantRightHalfDrawnAtConstantStep = true
  discontinuityAtMidpoint :
    setup.figure.stepBeginsAtMidpoint = true
  bothPanelsHaveLeftHardWall :
    ∀ panel : DiagramPanel,
      setup.figure.leftBoundaryIsHardWall panel = true
  bothPanelsHaveRightHardWall :
    ∀ panel : DiagramPanel,
      setup.figure.rightBoundaryIsHardWall panel = true

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalInfiniteSquareWellParameters
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  particleMassPositive : 0 < massInKilograms setup.particleMass
  wellWidthPositive : 0 < lengthInMeters setup.wellWidth
  stepHeightPositive : 0 < energyInJoules setup.perturbationStepHeight

/-!
Finite-potential profile in the interior of the hard-wall box.  This is the
figure's step profile, not a statement about the requested energy correction.
-/
structure SatisfiesRightHalfStepPotentialLaw
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  unperturbedPotentialIsZeroInside :
    ∀ xMeters : ℝ,
      xMeters ∈ Set.Icc 0 (lengthInMeters setup.wellWidth) →
      setup.unperturbedPotentialEnergyInJoules xMeters = 0
  perturbationIsZeroOnLeftHalf :
    ∀ xMeters : ℝ,
      xMeters ∈ Set.Ico 0 (lengthInMeters setup.wellWidth / 2) →
      setup.perturbingPotentialEnergyInJoules xMeters = 0
  perturbationEqualsVZeroOnRightHalf :
    ∀ xMeters : ℝ,
      xMeters ∈
          Set.Icc (lengthInMeters setup.wellWidth / 2)
            (lengthInMeters setup.wellWidth) →
      setup.perturbingPotentialEnergyInJoules xMeters =
        energyInJoules setup.perturbationStepHeight
  resultantIsSumInside :
    ∀ xMeters : ℝ,
      xMeters ∈ Set.Icc 0 (lengthInMeters setup.wellWidth) →
      setup.resultantPotentialEnergyInJoules xMeters =
        setup.unperturbedPotentialEnergyInJoules xMeters +
          setup.perturbingPotentialEnergyInJoules xMeters

/-! Hard-wall conditions for every unperturbed mode. -/
structure SatisfiesInfiniteRigidWallBoundaryConditions
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  leftWallNode :
    ∀ n : ℕ+, (setup.eigenstate n).amplitudePerSqrtMeter 0 = 0
  rightWallNode :
    ∀ n : ℕ+,
      (setup.eigenstate n).amplitudePerSqrtMeter
        (lengthInMeters setup.wellWidth) = 0
  wavefunctionVanishesOutsideWell :
    ∀ n : ℕ+, ∀ xMeters : ℝ,
      (xMeters < 0 ∨ lengthInMeters setup.wellWidth < xMeters) →
      (setup.eigenstate n).amplitudePerSqrtMeter xMeters = 0

/-!
Normalized stationary states and energy spectrum for an infinite square
well.  Neither clause constrains the first-order correction.
-/
structure SatisfiesInfiniteSquareWellEigenstateLaws
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  normalizedSineEigenfunctionInside :
    ∀ n : ℕ+, ∀ xMeters : ℝ,
      xMeters ∈ Set.Icc 0 (lengthInMeters setup.wellWidth) →
      (setup.eigenstate n).amplitudePerSqrtMeter xMeters =
        Complex.ofReal
          (Real.sqrt (2 / lengthInMeters setup.wellWidth) *
            Real.sin
              (((n : ℕ) : ℝ) * Real.pi * xMeters /
                lengthInMeters setup.wellWidth))
  totalProbabilityIsOne :
    ∀ n : ℕ+,
      (∫ xMeters : ℝ,
        Complex.normSq
          ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)) = 1
  unperturbedEnergyQuantization :
    ∀ n : ℕ+,
      energyInJoules (setup.eigenstate n).unperturbedEnergy =
        (((n : ℕ) : ℝ) ^ 2 * Real.pi ^ 2 * (Constants.ℏ : ℝ) ^ 2) /
          (2 * massInKilograms setup.particleMass *
            lengthInMeters setup.wellWidth ^ 2)

/-!
First-order stationary perturbation theory in SI readouts:
`ΔEₙ⁽¹⁾ = ∫₀ᴸ V'(x) |ψₙ(x)|² dx`.

This general expectation-value law constrains the independent correction
observable but does not evaluate the integral or state the requested answer.
-/
structure SatisfiesFirstOrderStationaryPerturbationTheory
    (setup : StepPerturbedInfiniteSquareWellSetup) : Prop where
  firstOrderCorrectionIsExpectationValue :
    ∀ n : ℕ+,
      energyInJoules (setup.firstOrderEnergyCorrection n) =
        ∫ xMeters in (0 : ℝ)..lengthInMeters setup.wellWidth,
          setup.perturbingPotentialEnergyInJoules xMeters *
            Complex.normSq
              ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)

/-! ## Answer choices and target conclusions -/

/-- Labels of the four correction choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Fraction of the step height printed beside each answer label. -/
def displayedCorrectionFraction : AnswerChoice → NNReal
  | .A => 1 / 7
  | .B => 1 / 5
  | .C => 1 / 3
  | .D => 1 / 2

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Every level's correction agrees with the energy printed by a choice. -/
def MatchesAnswerChoice
    (setup : StepPerturbedInfiniteSquareWellSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ n : ℕ+,
    setup.firstOrderEnergyCorrection n =
      displayedCorrectionFraction choice • setup.perturbationStepHeight

/-- A choice is the unique displayed correction compatible with all levels. -/
def IsUniqueMatchingAnswerChoice
    (setup : StepPerturbedInfiniteSquareWellSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Reflection symmetry (equivalently, direct integration of the normalized sine)
puts half the probability of every positive square-well mode in `[L/2,L]`.
-/
lemma probabilityInRightHalf_eq_oneHalf
    (setup : StepPerturbedInfiniteSquareWellSetup)
    (hPhysical : HasPhysicalInfiniteSquareWellParameters setup)
    (hBoundary : SatisfiesInfiniteRigidWallBoundaryConditions setup)
    (hEigenstates : SatisfiesInfiniteSquareWellEigenstateLaws setup) :
    ∀ n : ℕ+,
      (∫ xMeters in
          (lengthInMeters setup.wellWidth / 2)..
            lengthInMeters setup.wellWidth,
        Complex.normSq
          ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)) =
        (1 / 2 : ℝ) := by
  intro n
  let L : ℝ := lengthInMeters setup.wellWidth
  let k : ℝ := ((n : ℕ) : ℝ) * Real.pi / L
  have hL : 0 < L := by
    exact hPhysical.wellWidthPositive
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast n.pos
  have hk : k ≠ 0 := by
    dsimp [k]
    positivity
  have hsin_right : Real.sin (k * L) = 0 := by
    rw [show k * L = ((n : ℕ) : ℝ) * Real.pi by
      dsimp [k]
      field_simp]
    exact Real.sin_nat_mul_pi n
  have hsin_cos_mid :
      Real.sin (k * (L / 2)) * Real.cos (k * (L / 2)) = 0 := by
    have hdouble :
        2 * (k * (L / 2)) = ((n : ℕ) : ℝ) * Real.pi := by
      dsimp [k]
      field_simp
    have hs := Real.sin_two_mul (k * (L / 2))
    rw [hdouble, Real.sin_nat_mul_pi] at hs
    nlinarith
  calc
    (∫ xMeters in L / 2..L,
        Complex.normSq
          ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)) =
        ∫ xMeters in L / 2..L,
          (2 / L) * Real.sin (k * xMeters) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro xMeters hx
      have hxWell : xMeters ∈ Set.Icc 0 L := by
        rw [Set.uIcc_of_le (by linarith : L / 2 ≤ L)] at hx
        exact ⟨by linarith [hx.1], hx.2⟩
      change
        Complex.normSq
            ((setup.eigenstate n).amplitudePerSqrtMeter xMeters) =
          (2 / L) * Real.sin (k * xMeters) ^ 2
      rw [hEigenstates.normalizedSineEigenfunctionInside n xMeters
        (by simpa [L] using hxWell)]
      rw [Complex.normSq_ofReal]
      rw [show
        ((n : ℕ) : ℝ) * Real.pi * xMeters / L = k * xMeters by
          dsimp [k]
          ring]
      calc
        (Real.sqrt (2 / L) * Real.sin (k * xMeters)) *
              (Real.sqrt (2 / L) * Real.sin (k * xMeters)) =
            Real.sqrt (2 / L) ^ 2 * Real.sin (k * xMeters) ^ 2 := by
          ring
        _ = (2 / L) * Real.sin (k * xMeters) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]
    _ = (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_mul_left
        (fun y : ℝ => Real.sin y ^ 2) hk]
      rw [integral_sin_sq]
      rw [hsin_right, hsin_cos_mid]
      dsimp [k]
      field_simp
      ring

/-!
For every level the right-half step samples exactly half the normalized state,
so the first-order correction is the physical energy `V₀/2`, corresponding
uniquely to answer D.

This formalizes `thm:physics:phyx_mini_0545:target`.  The conclusion is not a
field of the setup and does not occur in any governing-law or figure premise.
-/
theorem problem_phyx_mini_0545
    (setup : StepPerturbedInfiniteSquareWellSetup)
    (hScenario : MatchesInfiniteSquareWellStepScenario setup)
    (hFigure : MatchesSuppliedPotentialDiagrams setup)
    (hPhysical : HasPhysicalInfiniteSquareWellParameters setup)
    (hPotential : SatisfiesRightHalfStepPotentialLaw setup)
    (hBoundary : SatisfiesInfiniteRigidWallBoundaryConditions setup)
    (hEigenstates : SatisfiesInfiniteSquareWellEigenstateLaws setup)
    (hPerturbationTheory :
      SatisfiesFirstOrderStationaryPerturbationTheory setup) :
    (∀ n : ℕ+,
      setup.firstOrderEnergyCorrection n =
        (1 / 2 : NNReal) • setup.perturbationStepHeight) ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hCorrectionReadout :
      ∀ n : ℕ+,
        energyInJoules (setup.firstOrderEnergyCorrection n) =
          (1 / 2 : ℝ) *
            energyInJoules setup.perturbationStepHeight := by
    intro n
    let L : ℝ := lengthInMeters setup.wellWidth
    let V : ℝ := energyInJoules setup.perturbationStepHeight
    let density : ℝ → ℝ := fun xMeters =>
      Complex.normSq
        ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)
    let integrand : ℝ → ℝ := fun xMeters =>
      setup.perturbingPotentialEnergyInJoules xMeters *
        density xMeters
    have hL : 0 < L := by
      exact hPhysical.wellWidthPositive
    have hProbability :
        (∫ xMeters in L / 2..L, density xMeters) =
          (1 / 2 : ℝ) := by
      simpa [L, density] using
        probabilityInRightHalf_eq_oneHalf
          setup hPhysical hBoundary hEigenstates n
    have hDensityRight :
        IntervalIntegrable density MeasureTheory.volume (L / 2) L := by
      let explicitDensity : ℝ → ℝ := fun xMeters =>
        Complex.normSq
          (Complex.ofReal
            (Real.sqrt (2 / L) *
              Real.sin
                (((n : ℕ) : ℝ) * Real.pi * xMeters / L)))
      have hExplicitDensity :
          IntervalIntegrable explicitDensity MeasureTheory.volume
            (L / 2) L := by
        dsimp [explicitDensity]
        apply Continuous.intervalIntegrable
        fun_prop
      apply hExplicitDensity.congr_uIoo
      intro xMeters hx
      rw [Set.uIoo_of_le (by linarith : L / 2 ≤ L)] at hx
      have hxWell : xMeters ∈ Set.Icc 0 L :=
        ⟨by linarith [hx.1], hx.2.le⟩
      change
        Complex.normSq
            (Complex.ofReal
              (Real.sqrt (2 / L) *
                Real.sin
                  (((n : ℕ) : ℝ) * Real.pi * xMeters / L))) =
          Complex.normSq
            ((setup.eigenstate n).amplitudePerSqrtMeter xMeters)
      rw [hEigenstates.normalizedSineEigenfunctionInside n xMeters
        (by simpa [L] using hxWell)]
    have hIntegrableLeft :
        IntervalIntegrable integrand MeasureTheory.volume 0 (L / 2) := by
      apply
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
            MeasureTheory.volume 0 (L / 2)).congr_uIoo
      intro xMeters hx
      rw [Set.uIoo_of_le (by linarith : (0 : ℝ) ≤ L / 2)] at hx
      change 0 = integrand xMeters
      dsimp [integrand]
      rw [hPotential.perturbationIsZeroOnLeftHalf xMeters
        ⟨hx.1.le, hx.2⟩]
      simp
    have hIntegrableRight :
        IntervalIntegrable integrand MeasureTheory.volume (L / 2) L := by
      apply (hDensityRight.const_mul V).congr_uIoo
      intro xMeters hx
      rw [Set.uIoo_of_le (by linarith : L / 2 ≤ L)] at hx
      change V * density xMeters = integrand xMeters
      dsimp [integrand]
      rw [hPotential.perturbationEqualsVZeroOnRightHalf xMeters
        (by simpa [L] using
          (show xMeters ∈ Set.Icc (L / 2) L from
            ⟨hx.1.le, hx.2.le⟩))]
    have hLeftIntegral :
        (∫ xMeters in 0..L / 2, integrand xMeters) = 0 := by
      calc
        (∫ xMeters in 0..L / 2, integrand xMeters) =
            ∫ _xMeters in 0..L / 2, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_uIoo
          intro xMeters hx
          rw [Set.uIoo_of_le (by linarith : (0 : ℝ) ≤ L / 2)] at hx
          dsimp [integrand]
          rw [hPotential.perturbationIsZeroOnLeftHalf xMeters
            ⟨hx.1.le, hx.2⟩]
          simp
        _ = 0 := by simp
    have hRightIntegral :
        (∫ xMeters in L / 2..L, integrand xMeters) =
          V * (1 / 2 : ℝ) := by
      calc
        (∫ xMeters in L / 2..L, integrand xMeters) =
            ∫ xMeters in L / 2..L, V * density xMeters := by
          apply intervalIntegral.integral_congr
          intro xMeters hx
          rw [Set.uIcc_of_le (by linarith : L / 2 ≤ L)] at hx
          dsimp [integrand]
          rw [hPotential.perturbationEqualsVZeroOnRightHalf xMeters
            (by simpa [L] using hx)]
        _ = V * (∫ xMeters in L / 2..L, density xMeters) := by
          rw [intervalIntegral.integral_const_mul]
        _ = V * (1 / 2 : ℝ) := by rw [hProbability]
    rw [hPerturbationTheory.firstOrderCorrectionIsExpectationValue n]
    change
      (∫ xMeters in 0..L, integrand xMeters) =
        (1 / 2 : ℝ) * V
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hIntegrableLeft hIntegrableRight]
    rw [hLeftIntegral, hRightIntegral]
    ring
  have hCorrection :
      ∀ n : ℕ+,
        setup.firstOrderEnergyCorrection n =
          (1 / 2 : NNReal) • setup.perturbationStepHeight := by
    intro n
    have hAtSI :
        setup.firstOrderEnergyCorrection n UnitChoices.SI =
          ((1 / 2 : NNReal) • setup.perturbationStepHeight)
            UnitChoices.SI := by
      apply WithDim.ext
      simpa [energyInJoules, Dimensionful.smul_apply,
        WithDim.smul_val, NNReal.smul_def] using hCorrectionReadout n
    apply Dimensionful.ext
    funext units
    rw [(setup.firstOrderEnergyCorrection n).property
      UnitChoices.SI units,
      ((1 / 2 : NNReal) • setup.perturbationStepHeight).property
        UnitChoices.SI units,
      hAtSI]
  constructor
  · exact hCorrection
  · constructor
    · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
        displayedCorrectionFraction] using hCorrection
    · intro other hOther
      have hScaledEnergies :
          displayedCorrectionFraction other •
              setup.perturbationStepHeight =
            (1 / 2 : NNReal) • setup.perturbationStepHeight :=
        (hOther (1 : ℕ+)).symm.trans (hCorrection (1 : ℕ+))
      have hScaledReadouts :=
        congrArg energyInJoules hScaledEnergies
      have hStepPositive :
          0 < energyInJoules setup.perturbationStepHeight :=
        hPhysical.stepHeightPositive
      change
        0 < (setup.perturbationStepHeight UnitChoices.SI).val
          at hStepPositive
      cases other with
      | A =>
          exfalso
          apply (ne_of_gt hStepPositive)
          norm_num [displayedCorrectionFraction, energyInJoules,
            Dimensionful.smul_apply, WithDim.smul_val,
            NNReal.smul_def] at hScaledReadouts
          exact hScaledReadouts
      | B =>
          exfalso
          apply (ne_of_gt hStepPositive)
          norm_num [displayedCorrectionFraction, energyInJoules,
            Dimensionful.smul_apply, WithDim.smul_val,
            NNReal.smul_def] at hScaledReadouts
          exact hScaledReadouts
      | C =>
          exfalso
          apply (ne_of_gt hStepPositive)
          norm_num [displayedCorrectionFraction, energyInJoules,
            Dimensionful.smul_apply, WithDim.smul_val,
            NNReal.smul_def] at hScaledReadouts
          exact hScaledReadouts
      | D =>
          rfl

end PhyXMiniProblems.ProblemPhyXMini0545
