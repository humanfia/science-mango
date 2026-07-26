import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0603

open Dimension
open scoped BigOperators

/-!
# Ground-state energy of spinless conduction electrons in a metal

A monovalent sample contains `N` atoms and hence `N` conduction electrons.
Ignoring spin, Pauli exclusion permits at most one electron in each
one-dimensional infinite-square-well level.  The metal is modelled as a well
whose displayed width is `N a`, where `a` is the atomic length scale.

Lengths, mass, action, and energy are represented by Physlib dimensionful
quantities.  Real numbers occur only as coherent-SI readouts or dimensionless
counts and ratios.

Assumption/target split:

* `MatchesMonovalentMetalScenario` records the electron, monovalent-metal,
  spin-ignored, one-dimensional infinite-well model and one free electron per
  atom;
* `MatchesSuppliedMetalWellFigure` records the literal boundaries, circles,
  ellipsis, span arrow, and `N a` width label in image 603;
* `HasPhysicalMetalWellParameters` and `SatisfiesInfiniteSquareWellSpectrum`
  state positivity and the general single-particle spectrum;
* `SatisfiesSpinlessFermionGroundState` states Pauli occupancy, additive
  energy, and minimization over all admissible occupations; and
* the closed form for the lowest total energy occurs only in
  `problem_phyx_mini_0603` and the displayed-answer table.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action such as reduced Planck action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in coherent SI units, metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical mass in coherent SI units, kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical action in coherent SI units, joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read a physical energy in coherent SI units, joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Physical setup and primary-figure vocabulary -/

/-- Particle species singled out by the problem statement. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Valence model for the metal atoms. -/
inductive MetalValenceModel where
  | monovalent
  | other
  deriving DecidableEq, Repr

/-- Whether electron spin degeneracy is retained in the occupancy count. -/
inductive SpinTreatment where
  | ignored
  | included
  deriving DecidableEq, Repr

/-- Confining potential used for the delocalized electrons. -/
inductive ConfinementModel where
  | infiniteSquareWell
  | other
  deriving DecidableEq, Repr

/-- Literal graphical features visible in image `603.png`. -/
inductive FigureFeature where
  | leftVerticalBoundary
  | rightVerticalBoundary
  | horizontalWellFloor
  | openConstituentCircles
  | continuationEllipsis
  | doubleHeadedWidthArrow
  | widthLabelN
  | widthLabelA
  deriving DecidableEq, Fintype, Repr

/-- Semantic reading of the width annotation printed below the well. -/
inductive FigureWidthLabel where
  | atomCountTimesAtomicLength
  deriving DecidableEq, Repr

/-- Literal visual data transcribed from the supplied metal-well diagram. -/
structure MetalWellFigure where
  featureShown : FigureFeature → Bool
  visibleOpenCircleCount : ℕ
  widthLabel : FigureWidthLabel

/-!
Independent physical quantities in the model.  In particular,
`groundStateEnergy` is an unconstrained dimensionful field here: it is not
defined from any answer choice or from the requested closed form.
-/
structure MetalWellSetup where
  particleSpecies : ParticleSpecies
  valenceModel : MetalValenceModel
  spinTreatment : SpinTreatment
  spatialDimension : ℕ
  confinementModel : ConfinementModel
  atomCount : ℕ
  conductionElectronCount : ℕ
  atomicLengthScale : LengthQuantity
  metalWellWidth : LengthQuantity
  electronMass : MassQuantity
  reducedPlanckAction : ActionQuantity
  energyLevel : ℕ → DimEnergy
  occupiedLevels : Finset ℕ
  groundStateEnergy : DimEnergy
  figure : MetalWellFigure

/-! ## Scenario, figure/data readouts, and governing physics -/

/--
The prose model: a monovalent metal contributes one conduction electron per
atom, spin is ignored, and the electrons occupy a one-dimensional infinite
square well.
-/
structure MatchesMonovalentMetalScenario (setup : MetalWellSetup) : Prop where
  particlesAreElectrons : setup.particleSpecies = .electron
  metalIsMonovalent : setup.valenceModel = .monovalent
  electronSpinIsIgnored : setup.spinTreatment = .ignored
  oneSpatialDimension : setup.spatialDimension = 1
  confinementIsInfiniteSquareWell :
    setup.confinementModel = .infiniteSquareWell
  oneConductionElectronPerAtom :
    setup.conductionElectronCount = setup.atomCount

/-!
Primary-image evidence: two walls and a floor bound the well, eight open
circles are explicitly drawn with an ellipsis for continuation, and the
double-headed span arrow is labelled `N a`.  The last field is the calibrated
physical reading of that label, not an energy conclusion.
-/
structure MatchesSuppliedMetalWellFigure (setup : MetalWellSetup) : Prop where
  everyNamedFeatureIsShown : ∀ feature, setup.figure.featureShown feature = true
  eightOpenCirclesAreExplicitlyDrawn :
    setup.figure.visibleOpenCircleCount = 8
  displayedWidthLabelIsNa :
    setup.figure.widthLabel = .atomCountTimesAtomicLength
  widthReadoutMatchesNa :
    lengthInMeters setup.metalWellWidth =
      (setup.atomCount : ℝ) * lengthInMeters setup.atomicLengthScale

/-- Positivity conditions selecting a nondegenerate physical metal sample. -/
structure HasPhysicalMetalWellParameters (setup : MetalWellSetup) : Prop where
  positiveAtomCount : 0 < setup.atomCount
  positiveConductionElectronCount : 0 < setup.conductionElectronCount
  positiveAtomicLengthScale : 0 < lengthInMeters setup.atomicLengthScale
  positiveMetalWellWidth : 0 < lengthInMeters setup.metalWellWidth
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  positiveReducedPlanckAction :
    0 < actionInJouleSeconds setup.reducedPlanckAction

/-!
The one-dimensional infinite-square-well spectrum

`E_n = n^2 * pi^2 * hbar^2 / (2 m L^2)`

for every positive quantum number.  Physlib currently has no dedicated
infinite-square-well spectrum declaration, so this is a local governing-law
interface rather than the requested total-energy formula.
-/
structure SatisfiesInfiniteSquareWellSpectrum (setup : MetalWellSetup) : Prop where
  energySpectrum : ∀ n : ℕ, 0 < n →
    energyInJoules (setup.energyLevel n) =
      ((n : ℝ) ^ 2 * Real.pi ^ 2 *
          actionInJouleSeconds setup.reducedPlanckAction ^ 2) /
        (2 * massInKilograms setup.electronMass *
          lengthInMeters setup.metalWellWidth ^ 2)

/-!
An admissible spinless occupation of `N` electrons is a finite set of exactly
`N` positive quantum numbers.  Use of a `Finset` expresses the Pauli rule that
no level is occupied more than once when spin degeneracy is ignored.
-/
def IsAdmissibleSpinlessOccupation
    (setup : MetalWellSetup) (levels : Finset ℕ) : Prop :=
  levels.card = setup.conductionElectronCount ∧
    ∀ n ∈ levels, 0 < n

/-!
The ground-state governing principle.  The setup's occupied levels form an
admissible Pauli occupation, the total energy is additive over them, and that
sum is minimal among every admissible occupation.  This predicate contains no
closed form for the minimum and no answer-choice value.
-/
structure SatisfiesSpinlessFermionGroundState (setup : MetalWellSetup) : Prop where
  occupiedLevelsAreAdmissible :
    IsAdmissibleSpinlessOccupation setup setup.occupiedLevels
  groundEnergyIsOccupiedLevelSum :
    energyInJoules setup.groundStateEnergy =
      ∑ n ∈ setup.occupiedLevels, energyInJoules (setup.energyLevel n)
  minimizesOverAdmissibleOccupations : ∀ levels : Finset ℕ,
    IsAdmissibleSpinlessOccupation setup levels →
      (∑ n ∈ setup.occupiedLevels, energyInJoules (setup.energyLevel n)) ≤
        ∑ n ∈ levels, energyInJoules (setup.energyLevel n)

/-! ## Displayed-answer semantics and target -/

/-- Labels attached to the four symbolic energy expressions in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/--
The single-atom ground-level energy scale
`pi^2 hbar^2 / (2 m_e a^2)`, expressed in joules.
-/
def singleAtomEnergyScaleInJoules (setup : MetalWellSetup) : ℝ :=
  (Real.pi ^ 2 * actionInJouleSeconds setup.reducedPlanckAction ^ 2) /
    (2 * massInKilograms setup.electronMass *
      lengthInMeters setup.atomicLengthScale ^ 2)

/-- The four symbolic energy expressions printed beside choices A--D. -/
def displayedEnergyInJoules
    (setup : MetalWellSetup) : AnswerChoice → ℝ
  | .A =>
      ((setup.atomCount : ℝ) * Real.pi ^ 2 *
          actionInJouleSeconds setup.reducedPlanckAction ^ 2) /
        (2 * massInKilograms setup.electronMass *
          ((setup.atomCount : ℝ) *
            lengthInMeters setup.atomicLengthScale) ^ 2)
  | .B =>
      singleAtomEnergyScaleInJoules setup *
        ((setup.atomCount : ℝ) ^ 2 / 6)
  | .C =>
      singleAtomEnergyScaleInJoules setup *
        (((setup.atomCount : ℝ) + 1) *
          (2 * (setup.atomCount : ℝ) + 1) /
          (6 * (setup.atomCount : ℝ)))
  | .D =>
      (setup.atomCount : ℝ) * singleAtomEnergyScaleInJoules setup

/-- Dataset metadata recording answer C; it is not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- The physical ground-state energy agrees with one displayed expression. -/
def MatchesDisplayedEnergyChoice
    (setup : MetalWellSetup) (choice : AnswerChoice) : Prop :=
  energyInJoules setup.groundStateEnergy =
    displayedEnergyInJoules setup choice

/-!
Filling the lowest `N` distinct square-well levels gives

`E_ground = [pi^2 hbar^2 / (2 m_e a^2)]
              * [(N + 1)(2N + 1) / (6N)]`,

which is displayed choice C.

This formalizes `thm:physics:phyx_mini_0603:target`.  The closed form and
choice C do not occur in any theorem premise.
-/
theorem problem_phyx_mini_0603
    (setup : MetalWellSetup)
    (_scenario : MatchesMonovalentMetalScenario setup)
    (_figure : MatchesSuppliedMetalWellFigure setup)
    (_physical : HasPhysicalMetalWellParameters setup)
    (_spectrum : SatisfiesInfiniteSquareWellSpectrum setup)
    (_groundState : SatisfiesSpinlessFermionGroundState setup) :
    energyInJoules setup.groundStateEnergy =
        singleAtomEnergyScaleInJoules setup *
          (((setup.atomCount : ℝ) + 1) *
            (2 * (setup.atomCount : ℝ) + 1) /
            (6 * (setup.atomCount : ℝ))) ∧
      MatchesDisplayedEnergyChoice setup .C := by
  let lowestLevels : Finset ℕ :=
    Finset.image
      (fun i : Fin setup.atomCount => (i : ℕ) + 1)
      Finset.univ
  let wellEnergyScale : ℝ :=
    (Real.pi ^ 2 *
        actionInJouleSeconds setup.reducedPlanckAction ^ 2) /
      (2 * massInKilograms setup.electronMass *
        lengthInMeters setup.metalWellWidth ^ 2)
  -- All denominators and the common well-energy scale are nonzero and positive.
  have h_atom_count_ne : (setup.atomCount : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt _physical.positiveAtomCount)
  have h_mass_ne : massInKilograms setup.electronMass ≠ 0 :=
    ne_of_gt _physical.positiveElectronMass
  have h_atomic_length_ne :
      lengthInMeters setup.atomicLengthScale ≠ 0 :=
    ne_of_gt _physical.positiveAtomicLengthScale
  have h_well_energy_scale_pos : 0 < wellEnergyScale := by
    dsimp [wellEnergyScale]
    apply div_pos
    · exact mul_pos
        (sq_pos_of_pos Real.pi_pos)
        (sq_pos_of_pos _physical.positiveReducedPlanckAction)
    · exact mul_pos
        (mul_pos (by norm_num) _physical.positiveElectronMass)
        (sq_pos_of_pos _physical.positiveMetalWellWidth)
  -- The elementary finite sum of the first `n` positive squares.
  have sum_squares (n : ℕ) :
      (∑ i : Fin n, (((i.val + 1 : ℕ) : ℝ) ^ 2)) =
        (n : ℝ) * ((n : ℝ) + 1) *
          (2 * (n : ℝ) + 1) / 6 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, ih]
        push_cast
        ring
  -- Increasing enumeration shows that the `i`th occupied level is at least `i + 1`.
  have sum_squares_le_of_admissible
      (levels : Finset ℕ)
      (hlevels : IsAdmissibleSpinlessOccupation setup levels) :
      (∑ i : Fin setup.atomCount,
          (((i.val + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ n ∈ levels, ((n : ℝ) ^ 2) := by
    have hcard : levels.card = setup.atomCount := by
      calc
        levels.card = setup.conductionElectronCount := hlevels.1
        _ = setup.atomCount := _scenario.oneConductionElectronPerAtom
    let e : Fin setup.atomCount ↪o ℕ :=
      levels.orderEmbOfFin hcard
    have he_mem (i : Fin setup.atomCount) : e i ∈ levels := by
      exact levels.orderEmbOfFin_mem hcard i
    have he_pos (i : Fin setup.atomCount) : 0 < e i :=
      hlevels.2 (e i) (he_mem i)
    have positive_orderEmb_lower :
        ∀ {k : ℕ} (embedding : Fin k ↪o ℕ),
          (∀ i : Fin k, 0 < embedding i) →
          ∀ i : Fin k, (i : ℕ) + 1 ≤ embedding i := by
      intro k embedding hembedding_pos i
      cases k with
      | zero => exact Fin.elim0 i
      | succ n =>
          induction i using Fin.induction with
          | zero =>
              change 1 ≤ embedding (0 : Fin (n + 1))
              exact hembedding_pos 0
          | succ i ih =>
              have hlt : embedding i.castSucc < embedding i.succ :=
                embedding.strictMono Fin.castSucc_lt_succ
              change (i : ℕ) + 1 + 1 ≤ embedding i.succ
              change (i : ℕ) + 1 ≤ embedding i.castSucc at ih
              omega
    have he_lower (i : Fin setup.atomCount) :
        (i : ℕ) + 1 ≤ e i :=
      positive_orderEmb_lower e he_pos i
    have hsum :
        (∑ n ∈ levels, ((n : ℝ) ^ 2)) =
          ∑ i : Fin setup.atomCount, (((e i : ℕ) : ℝ) ^ 2) := by
      rw [← levels.map_orderEmbOfFin_univ hcard, Finset.sum_map]
      simp [e]
    rw [hsum]
    apply Finset.sum_le_sum
    intro i _
    have hcast :
        (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ((e i : ℕ) : ℝ) := by
      exact_mod_cast he_lower i
    have hnonneg :
        0 ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith
  -- Every positive-level energy sum is the common well scale times a square sum.
  have energy_sum_eq_scale_mul
      (levels : Finset ℕ)
      (hlevels_pos : ∀ n ∈ levels, 0 < n) :
      (∑ n ∈ levels, energyInJoules (setup.energyLevel n)) =
        wellEnergyScale * ∑ n ∈ levels, ((n : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [_spectrum.energySpectrum n (hlevels_pos n hn)]
    dsimp [wellEnergyScale]
    ring
  -- The first `N` positive levels form a valid Pauli occupation.
  have h_lowest_admissible :
      IsAdmissibleSpinlessOccupation setup lowestLevels := by
    constructor
    · calc
        lowestLevels.card = setup.atomCount := by
          dsimp [lowestLevels]
          rw [Finset.card_image_of_injective]
          · simp
          · intro i j hij
            exact Fin.ext (Nat.add_right_cancel hij)
        _ = setup.conductionElectronCount :=
          _scenario.oneConductionElectronPerAtom.symm
    · intro n hn
      dsimp [lowestLevels] at hn
      rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
      exact Nat.succ_pos i
  -- Reindex the candidate occupation by `Fin N`.
  have h_lowest_squares :
      (∑ n ∈ lowestLevels, ((n : ℝ) ^ 2)) =
        ∑ i : Fin setup.atomCount,
          (((i.val + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [lowestLevels]
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Fin.ext (Nat.add_right_cancel hij)
  -- Apply the enumeration bound to the actual occupied levels.
  have h_occupied_squares_lower :
      (∑ i : Fin setup.atomCount,
          (((i.val + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ n ∈ setup.occupiedLevels, ((n : ℝ) ^ 2) :=
    sum_squares_le_of_admissible
      setup.occupiedLevels
      _groundState.occupiedLevelsAreAdmissible
  -- Minimality bounds the ground-state energy by the first-level occupation.
  have h_ground_energy_upper :
      energyInJoules setup.groundStateEnergy ≤
        wellEnergyScale *
          ∑ i : Fin setup.atomCount,
            (((i.val + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      energyInJoules setup.groundStateEnergy =
          ∑ n ∈ setup.occupiedLevels,
            energyInJoules (setup.energyLevel n) :=
        _groundState.groundEnergyIsOccupiedLevelSum
      _ ≤ ∑ n ∈ lowestLevels,
          energyInJoules (setup.energyLevel n) :=
        _groundState.minimizesOverAdmissibleOccupations
          lowestLevels h_lowest_admissible
      _ = wellEnergyScale *
          ∑ n ∈ lowestLevels, ((n : ℝ) ^ 2) :=
        energy_sum_eq_scale_mul
          lowestLevels h_lowest_admissible.2
      _ = wellEnergyScale *
          ∑ i : Fin setup.atomCount,
            (((i.val + 1 : ℕ) : ℝ) ^ 2) := by
        rw [h_lowest_squares]
  -- The enumeration bound supplies the converse inequality.
  have h_ground_energy_lower :
      wellEnergyScale *
          ∑ i : Fin setup.atomCount,
            (((i.val + 1 : ℕ) : ℝ) ^ 2) ≤
        energyInJoules setup.groundStateEnergy := by
    calc
      wellEnergyScale *
            ∑ i : Fin setup.atomCount,
              (((i.val + 1 : ℕ) : ℝ) ^ 2) ≤
          wellEnergyScale *
            ∑ n ∈ setup.occupiedLevels, ((n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          h_occupied_squares_lower
          h_well_energy_scale_pos.le
      _ = ∑ n ∈ setup.occupiedLevels,
          energyInJoules (setup.energyLevel n) := by
        symm
        exact energy_sum_eq_scale_mul
          setup.occupiedLevels
          _groundState.occupiedLevelsAreAdmissible.2
      _ = energyInJoules setup.groundStateEnergy :=
        _groundState.groundEnergyIsOccupiedLevelSum.symm
  -- Hence the minimizing energy is exactly the first-positive-level square sum.
  have h_ground_energy_fin_sum :
      energyInJoules setup.groundStateEnergy =
        wellEnergyScale *
          ∑ i : Fin setup.atomCount,
            (((i.val + 1 : ℕ) : ℝ) ^ 2) :=
    le_antisymm h_ground_energy_upper h_ground_energy_lower
  -- Evaluate the square sum and substitute the displayed width `N a`.
  have h_closed_form :
      energyInJoules setup.groundStateEnergy =
        singleAtomEnergyScaleInJoules setup *
          (((setup.atomCount : ℝ) + 1) *
            (2 * (setup.atomCount : ℝ) + 1) /
            (6 * (setup.atomCount : ℝ))) := by
    rw [h_ground_energy_fin_sum, sum_squares setup.atomCount]
    dsimp [wellEnergyScale, singleAtomEnergyScaleInJoules]
    rw [_figure.widthReadoutMatchesNa]
    field_simp [h_atom_count_ne, h_mass_ne, h_atomic_length_ne]
  -- Choice C is definitionally the same displayed closed form.
  constructor
  · exact h_closed_form
  · simpa [MatchesDisplayedEnergyChoice, displayedEnergyInJoules] using
      h_closed_form

end PhyXMiniProblems.ProblemPhyXMini0603
