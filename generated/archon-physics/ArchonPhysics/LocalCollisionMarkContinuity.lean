import ArchonPhysics.SimpleSpectrumProjectorContinuity
import ArchonPhysics.MarkedEmpiricalResonanceTransfer
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Local continuity of ordered collision marks

The projector formula for a squared interaction weight is globally measurable,
but it is continuous only away from spectral collisions. This module combines
the local projector theorem on the simple-spectrum locus with elementary
finite-sum continuity. It also isolates the second singularity in a physical
collision mark: inverse-frequency normalization is locally continuous when all
participating ordered frequencies are strictly positive.

These are deterministic localization statements. In particular, this file
does not assert a probabilistic tail bound for the minimum spectral gap or the
minimum positive frequency.
-/

open scoped Matrix

namespace ArchonPhysics.LocalCollisionMarkContinuity

open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.SimpleSpectrumProjectorContinuity

noncomputable section

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota]

/-- Joint bond-matrix and ordered-spectrum data. -/
abbrev BondSpectrumData (bond iota : Type*) [Fintype iota] :=
  Matrix bond iota Real × HermitianMatrix iota

/-- One ordered square-root frequency is continuous on the entire Hermitian
matrix space. -/
theorem continuous_orderedModeFrequency
    (k : Fin (Fintype.card iota)) :
    Continuous fun A : HermitianMatrix iota ↦ orderedModeFrequency A k := by
  exact Real.continuous_sqrt.comp (continuous_orderedEigenvalue k)

/-- Entrywise continuity of the projected bond kernel at a simple-spectrum
base point, jointly in the bond matrix and Hermitian matrix. -/
theorem continuousAt_projectedBondKernel_apply
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) (j l : bond) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        projectedBondKernel p.1 p.2 k j l) (B, A) := by
  unfold projectedBondKernel
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply tendsto_finsetSum Finset.univ
  intro u _hu
  apply ContinuousAt.mul
  · apply tendsto_finsetSum Finset.univ
    intro v _hv
    apply ContinuousAt.mul
    · fun_prop
    · exact (continuousAt_orderedModeProjector_apply A hsimple k v u).comp_of_eq
        continuousAt_snd rfl
  · fun_prop

/-- Matrix-valued form of local projected-kernel continuity. -/
theorem continuousAt_projectedBondKernel
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card iota)) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        projectedBondKernel p.1 p.2 k) (B, A) := by
  apply continuousAt_pi'
  intro j
  apply continuousAt_pi'
  intro l
  exact continuousAt_projectedBondKernel_apply B A hsimple k j l

/-- The basis-free squared interaction coefficient is jointly locally
continuous in `B` and `A` at every simple-spectrum base point. -/
theorem continuousAt_orderedInteractionWeightSq [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (modes : Fin n → Fin (Fintype.card iota)) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        orderedInteractionWeightSq p.1 p.2 modes) (B, A) := by
  unfold orderedInteractionWeightSq
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  apply tendsto_finsetSum Finset.univ
  intro l _hl
  apply tendsto_finsetProd Finset.univ
  intro r _hr
  exact continuousAt_projectedBondKernel_apply B A hsimple (modes r) j l

/-- Generic projector-based normalized ordered interaction weight. The
definition is total, while physical use requires every selected frequency to
be positive. -/
def orderedNormalizedInteractionWeight [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (modes : Fin n → Fin (Fintype.card iota)) : Real :=
  orderedInteractionWeightSq B A modes *
    ∏ r, (2 * orderedModeFrequency A (modes r))⁻¹

/-- Every ordered mode in a tuple has strictly positive frequency. -/
def PositiveOrderedModeTuple {n : Nat} (A : HermitianMatrix iota)
    (modes : Fin n → Fin (Fintype.card iota)) : Prop :=
  ∀ r, 0 < orderedModeFrequency A (modes r)

/-- A finite positive-frequency tuple stays in the positive sector throughout
some neighborhood of the base matrix. -/
theorem eventually_positiveOrderedModeTuple
    {n : Nat} (A : HermitianMatrix iota)
    (modes : Fin n → Fin (Fintype.card iota))
    (hpositive : PositiveOrderedModeTuple A modes) :
    ∀ᶠ A1 in nhds A, PositiveOrderedModeTuple A1 modes := by
  unfold PositiveOrderedModeTuple
  rw [Filter.eventually_all]
  intro r
  exact (continuous_orderedModeFrequency (modes r)).continuousAt.eventually
    (eventually_gt_nhds (hpositive r))

/-- Positive-frequency normalization introduces no further local instability:
the generic normalized squared weight is continuous at a simple-spectrum
base point whose participating modes are all positive. -/
theorem continuousAt_orderedNormalizedInteractionWeight [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (modes : Fin n → Fin (Fintype.card iota))
    (hpositive : PositiveOrderedModeTuple A modes) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        orderedNormalizedInteractionWeight p.1 p.2 modes) (B, A) := by
  unfold orderedNormalizedInteractionWeight
  apply (continuousAt_orderedInteractionWeightSq B A hsimple modes).mul
  apply tendsto_finsetProd Finset.univ
  intro r _hr
  have hfrequency : ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        orderedModeFrequency p.2 (modes r)) (B, A) :=
    (continuous_orderedModeFrequency (modes r)).continuousAt.comp_of_eq
      continuousAt_snd rfl
  exact (continuousAt_const.mul hfrequency).inv₀
    (mul_ne_zero (by norm_num) (ne_of_gt (hpositive r)))

/-- The signed ordered phase mismatch is continuous for every fixed finite
tuple. This part does not require simplicity or positivity. -/
theorem continuous_orderedPhaseMismatch
    {n : Nat} (sign : Fin n → InteractionSign)
    (modes : Fin n → Fin (Fintype.card iota)) :
    Continuous fun A : HermitianMatrix iota ↦
      orderedPhaseMismatch A sign modes := by
  unfold orderedPhaseMismatch
  apply continuous_finsetSum Finset.univ
  intro r _hr
  exact continuous_const.mul
    (continuous_orderedModeFrequency (modes r))

/-- Joint-data form of phase-mismatch continuity. -/
theorem continuousAt_orderedPhaseMismatch
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (sign : Fin n → InteractionSign)
    (modes : Fin n → Fin (Fintype.card iota)) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        orderedPhaseMismatch p.2 sign modes) (B, A) :=
  (continuous_orderedPhaseMismatch sign modes).continuousAt.comp_of_eq
    continuousAt_snd rfl

/-- A complete deterministic collision mark: signed mismatch and normalized
squared interaction weight. -/
def orderedCollisionMark [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (sign : Fin n → InteractionSign)
    (modes : Fin n → Fin (Fintype.card iota)) : Real × Real :=
  (orderedPhaseMismatch A sign modes,
    orderedNormalizedInteractionWeight B A modes)

/-- The generic normalization specializes definitionally to the harmonic
projector formula used by the random-mass collision data. -/
theorem orderedNormalizedInteractionWeight_harmonic_eq
    {N n : Nat} [NeZero N]
    (m : ArchonPhysics.Lattice.PositiveMassConfig N)
    (modes : Fin n → OrderedModeIndex N) :
    orderedNormalizedInteractionWeight
        (ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix m)
        (ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian m) modes =
      ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic.harmonicOrderedNormalizedInteractionWeight
        m modes := rfl

/-- For three waves the complete generic mark is exactly the existing
positive-collision mark before applying its sample-dependent positivity
filter. -/
theorem orderedCollisionMark_harmonic_eq
    {N : Nat} [NeZero N]
    (m : ArchonPhysics.Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    orderedCollisionMark
        (ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix m)
        (ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic.harmonicHermitian m)
        sign modes =
      orderedPositiveCollisionMark m sign modes := rfl

/-- The whole ordered collision mark is jointly locally continuous at a
simple-spectrum, positive-frequency base point. -/
theorem continuousAt_orderedCollisionMark [Fintype bond]
    {n : Nat} (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (sign : Fin n → InteractionSign)
    (modes : Fin n → Fin (Fintype.card iota))
    (hpositive : PositiveOrderedModeTuple A modes) :
    ContinuousAt
      (fun p : BondSpectrumData bond iota ↦
        orderedCollisionMark p.1 p.2 sign modes) (B, A) := by
  exact (continuousAt_orderedPhaseMismatch B A sign modes).prodMk
    (continuousAt_orderedNormalizedInteractionWeight
      B A hsimple modes hpositive)

end

end ArchonPhysics.LocalCollisionMarkContinuity
