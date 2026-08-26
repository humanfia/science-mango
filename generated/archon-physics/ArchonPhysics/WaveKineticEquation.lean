import Mathlib
import ArchonPhysics.EquipartitionEntropy

/-!
# Parameterized wave kinetic equation and modal-energy observables

This module supplies the first definition-level node of the effective kinetic
family.  A kinetic state records wave actions.  Modal energy is therefore
`omega * action`, rather than the action itself, and the finite late-window
observable reuses the normalization convention from
`ArchonPhysics.EquipartitionEntropy`.

`CollisionData.collision` is an explicitly supplied operator.  No integral
kernel, resonance measure, symmetry, positivity preservation, conservation
law, well-posedness, or relaxation theorem is asserted here.  Such properties
must be provided and proved by later, separately named contracts.
-/

namespace ArchonPhysics

noncomputable section

/-- A finite-mode kinetic state: the value at a mode is its wave action. -/
abbrev KineticState (ι : Type) := ι → Real

/--
Minimal data for a parameterized wave kinetic model.

The frequency and collision operator are data, not derived objects.  In
particular, this structure does not claim that `collision` is represented by
the exact collision kernel of any microscopic lattice.
-/
structure CollisionData (ι : Type) where
  /-- Mode frequency used to convert action into modal energy. -/
  omega : ι → Real
  /-- A supplied, coupling-independent collision map on action states. -/
  collision : KineticState ι → KineticState ι

/-- The explicitly parameterized right-hand side `g^2 C(D)`. -/
def waveKineticVectorField {ι : Type} (data : CollisionData ι) (g : Real)
    (D : KineticState ι) : KineticState ι :=
  g ^ 2 • data.collision D

/--
A trajectory solves the supplied wave kinetic initial-value equation.

This is only a predicate.  It neither constructs a trajectory nor asserts
uniqueness, positivity, conservation, or relaxation.
-/
def SolvesWaveKineticEquation {ι : Type} [Fintype ι]
    (data : CollisionData ι) (g : Real) (initial : KineticState ι)
    (D : Real → KineticState ι) : Prop :=
  D 0 = initial ∧
    ∀ t, HasDerivAt D (waveKineticVectorField data g (D t)) t

/-- The kinetic equation unfolds exactly to `D' = g^2 C(D)` and its initial value. -/
theorem solvesWaveKineticEquation_iff {ι : Type} [Fintype ι]
    (data : CollisionData ι) (g : Real) (initial : KineticState ι)
    (D : Real → KineticState ι) :
    SolvesWaveKineticEquation data g initial D ↔
      D 0 = initial ∧
        ∀ t, HasDerivAt D (g ^ 2 • data.collision (D t)) t := by
  rfl

/-- Modal energy is frequency times wave action, mode by mode. -/
def modalEnergy {ι : Type} (data : CollisionData ι) (D : KineticState ι) :
    ι → Real :=
  fun i => data.omega i * D i

/-- The modal-energy adapter is definitionally `omega * action`. -/
@[simp] theorem modalEnergy_apply {ι : Type} (data : CollisionData ι)
    (D : KineticState ι) (i : ι) :
    modalEnergy data D i = data.omega i * D i := by
  rfl

/-- Nonnegative frequencies and actions give nonnegative modal energies. -/
theorem modalEnergy_nonneg {ι : Type} (data : CollisionData ι)
    (D : KineticState ι) (homega : ∀ i, 0 ≤ data.omega i)
    (hD : ∀ i, 0 ≤ D i) : ∀ i, 0 ≤ modalEnergy data D i := by
  intro i
  exact mul_nonneg (homega i) (hD i)

/-- The late-window modal-energy observable associated with an action trajectory. -/
def lateWindowKineticEnergy {ι : Type} (data : CollisionData ι)
    (D : Real → KineticState ι) (mu T : Real) : ι → Real :=
  EquipartitionEntropy.lateWindowAverage
    (fun t => modalEnergy data (D t)) mu T

/-- The late-window adapter exposes its exact integral formula. -/
theorem lateWindowKineticEnergy_apply {ι : Type} (data : CollisionData ι)
    (D : Real → KineticState ι) (mu T : Real) (i : ι) :
    lateWindowKineticEnergy data D mu T i =
      ((1 - mu) * T)⁻¹ *
        ∫ t in mu * T..T, data.omega i * D t i := by
  rfl

/--
The normalized late-window modal-energy weights.  Positivity of their total is
not hidden in this definition and is required explicitly by normalization
theorems below.
-/
def normalizedLateWindowKineticEnergy {ι : Type} [Fintype ι]
    (data : CollisionData ι) (D : Real → KineticState ι) (mu T : Real) :
    ι → Real :=
  EquipartitionEntropy.normalizedWeights
    (lateWindowKineticEnergy data D mu T)

/-- The normalized adapter is exactly division by the finite total energy. -/
theorem normalizedLateWindowKineticEnergy_apply {ι : Type} [Fintype ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu T : Real) (i : ι) :
    normalizedLateWindowKineticEnergy data D mu T i =
      lateWindowKineticEnergy data D mu T i /
        EquipartitionEntropy.totalWeight
          (lateWindowKineticEnergy data D mu T) := by
  rfl

/--
The finite `l1` distance of normalized late-window modal energy from uniform
energy.  This deliberately compares `omega * action`, not uniform action.
-/
def kineticEquipartitionDistance {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu T : Real) : Real :=
  EquipartitionEntropy.l1Distance
    (normalizedLateWindowKineticEnergy data D mu T)
    (EquipartitionEntropy.uniformWeights : ι → Real)

/-- Approximate kinetic equipartition using the existing finite observable convention. -/
def KineticApproxEquipartition {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu delta T : Real) : Prop :=
  0 ≤ mu ∧ mu < 1 ∧ 0 < T ∧
    0 < EquipartitionEntropy.totalWeight
      (lateWindowKineticEnergy data D mu T) ∧
    kineticEquipartitionDistance data D mu T ≤ delta

/-- The distance adapter unfolds to the same normalized finite `l1` observable. -/
theorem kineticEquipartitionDistance_eq {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu T : Real) :
    kineticEquipartitionDistance data D mu T =
      EquipartitionEntropy.l1Distance
        (EquipartitionEntropy.normalizedWeights
          (EquipartitionEntropy.lateWindowAverage
            (fun t => modalEnergy data (D t)) mu T))
        (EquipartitionEntropy.uniformWeights : ι → Real) := by
  rfl

/-- The kinetic equipartition predicate has no hidden occurrence assumption. -/
theorem kineticApproxEquipartition_iff {ι : Type} [Fintype ι] [Nonempty ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu delta T : Real) :
    KineticApproxEquipartition data D mu delta T ↔
      0 ≤ mu ∧ mu < 1 ∧ 0 < T ∧
        0 < EquipartitionEntropy.totalWeight
          (lateWindowKineticEnergy data D mu T) ∧
        kineticEquipartitionDistance data D mu T ≤ delta := by
  rfl

/-- Nonnegative frequency and action make the late-window energy nonnegative. -/
theorem lateWindowKineticEnergy_nonneg {ι : Type} (data : CollisionData ι)
    (D : Real → KineticState ι) (mu T : Real)
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (homega : ∀ i, 0 ≤ data.omega i) (hD : ∀ t i, 0 ≤ D t i) :
    ∀ i, 0 ≤ lateWindowKineticEnergy data D mu T i := by
  unfold lateWindowKineticEnergy
  apply EquipartitionEntropy.lateWindowAverage_nonneg
  · exact hmu
  · exact hmu_lt_one
  · exact hT
  · intro t i
    exact mul_nonneg (homega i) (hD t i)

/-- Positive total late-window energy makes the normalized weights sum to one. -/
theorem sum_normalizedLateWindowKineticEnergy {ι : Type} [Fintype ι]
    (data : CollisionData ι) (D : Real → KineticState ι)
    (mu T : Real)
    (hpositive : 0 < EquipartitionEntropy.totalWeight
      (lateWindowKineticEnergy data D mu T)) :
    ∑ i, normalizedLateWindowKineticEnergy data D mu T i = 1 := by
  exact EquipartitionEntropy.sum_normalizedWeights
    (lateWindowKineticEnergy data D mu T) hpositive

end

end ArchonPhysics
