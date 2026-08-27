import ArchonPhysics.FreeFPUTMismatchPhaseExpansion
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Free FPUT mismatch as a random-mass collision mismatch

The exact free quadratic FPUT expansion labels its two inputs by phase or
conjugate-phase characters.  The collision modules instead label all three
legs by signs multiplying positive normal-mode frequencies.  This file gives
the exact finite-volume adapter between those conventions.

The observed leg has collision sign `plus`.  An input phase character has
charge `+1` and therefore collision sign `minus`, while an input conjugate
character has charge `-1` and therefore collision sign `plus`.  The first
identity works for an arbitrary supplied frequency.  Identification with
`phaseMismatch` and `orderedThreeWaveMismatch` is made only after specializing
that frequency to the random-mass harmonic spectrum.
-/

namespace ArchonPhysics.FreeFPUTCollisionMismatchBridge

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

/-- Convert an input phase charge to its sign in an output-minus-input
collision mismatch. -/
def phaseSignToInputInteractionSign : PhaseSign → InteractionSign
  | .phase => .minus
  | .conjugate => .plus

@[simp] theorem coefficient_phaseSignToInputInteractionSign
    (sign : PhaseSign) :
    (phaseSignToInputInteractionSign sign).coefficient =
      -(sign.exponent : Real) := by
  cases sign <;>
    simp [phaseSignToInputInteractionSign, PhaseSign.exponent,
      InteractionSign.coefficient]

/-- The two input interaction signs carried by a quadratic phase term. -/
def quadraticInputInteractionSign {N : Nat} [NeZero N]
    (term : QuadraticPhaseTerm N) : Fin 2 → InteractionSign :=
  Fin.cons (phaseSignToInputInteractionSign (binaryPhaseSign term.2.1))
    (fun _ ↦ phaseSignToInputInteractionSign (binaryPhaseSign term.2.2))

/-- The output-plus sign followed by the two input signs. -/
def quadraticCollisionSign {N : Nat} [NeZero N]
    (term : QuadraticPhaseTerm N) : Fin 3 → InteractionSign :=
  Fin.cons .plus (quadraticInputInteractionSign term)

/-- The observed output followed by the two quadratic input modes. -/
def quadraticCollisionModes {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    Fin 3 → Lattice.Site N :=
  Fin.cons observed term.1

private theorem sum_single_frequency {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (mode : Lattice.Site N)
    (exponent : Int) :
    (∑ other : Lattice.Site N,
      (((Pi.single mode exponent : Lattice.Site N → Int) other : Int) : Real) *
        frequency other) =
      (exponent : Real) * frequency mode := by
  classical
  rw [Fintype.sum_eq_single mode]
  · simp
  · intro other hne
    simp [hne]

/-- The phase charge of a quadratic term is exactly the signed sum of its two
input frequencies.  Repeated input modes are included with multiplicity. -/
theorem chargeFrequency_quadraticPhaseCharge {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) :
    chargeFrequency (quadraticPhaseCharge term) frequency =
      ((binaryPhaseSign term.2.1).exponent : Real) * frequency (term.1 0) +
      ((binaryPhaseSign term.2.2).exponent : Real) * frequency (term.1 1) := by
  classical
  unfold quadraticPhaseCharge binarySignedMode SignedMode.charge
  simp only [chargeFrequency, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib]
  rw [sum_single_frequency frequency (term.1 0)
    (binaryPhaseSign term.2.1).exponent]
  rw [sum_single_frequency frequency (term.1 1)
    (binaryPhaseSign term.2.2).exponent]
/-- For any externally supplied frequency, the FPUT mismatch equals the
three-leg output-plus signed collision sum. -/
theorem quadraticPhaseMismatch_eq_signedCollisionSum
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch frequency observed term =
      ∑ r, (quadraticCollisionSign term r).coefficient *
        frequency (quadraticCollisionModes observed term r) := by
  rw [quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    chargeFrequency_quadraticPhaseCharge, Fin.sum_univ_succ]
  simp only [quadraticCollisionSign, quadraticCollisionModes,
    Fin.cons_zero, Fin.cons_succ, InteractionSign.coefficient_plus, one_mul]
  rw [Fin.sum_univ_succ]
  simp only [quadraticInputInteractionSign, Fin.cons_zero, Fin.cons_succ,
    coefficient_phaseSignToInputInteractionSign]
  rw [Fin.sum_univ_one]
  norm_num
  ring

/-- Specializing the supplied frequency to the harmonic random-mass spectrum
turns the free FPUT mismatch into `ModalPhaseMismatch.phaseMismatch`. -/
theorem quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    quadraticPhaseMismatch (modeFrequency m) observed term =
      phaseMismatch m (quadraticCollisionSign term)
        (quadraticCollisionModes observed term) := by
  rw [quadraticPhaseMismatch_eq_signedCollisionSum]
  rfl

/-- Pull the canonical ordered harmonic frequency back to physical mode
indices. -/
def orderedPullbackFrequency {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mode : Lattice.Site N) : Real :=
  orderedModeFrequency (harmonicHermitian m) (orderedIndexEquiv.symm mode)

/-- Pulling the ordered spectrum back through its index equivalence recovers
the physical harmonic frequency function. -/
theorem orderedPullbackFrequency_eq_modeFrequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    orderedPullbackFrequency m = modeFrequency m := by
  funext mode
  unfold orderedPullbackFrequency
  rw [orderedModeFrequency_harmonicHermitian_eq]
  simp

/-- Turn one ordered three-wave tuple and two binary phase sectors into the
quadratic phase term with the first leg observed. -/
def orderedQuadraticPhaseTerm {N : Nat} [NeZero N]
    (modes : OrderedModeTriple N) (leftSign rightSign : Fin 2) :
    QuadraticPhaseTerm N :=
  (fun r ↦ orderedIndexEquiv (modes r.succ), (leftSign, rightSign))

/-- The physical mode triple of an ordered quadratic term is exactly the
ordered tuple transported through `orderedIndexEquiv`. -/
theorem quadraticCollisionModes_orderedQuadraticPhaseTerm
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N)
    (leftSign rightSign : Fin 2) :
    quadraticCollisionModes (orderedIndexEquiv (modes 0))
        (orderedQuadraticPhaseTerm modes leftSign rightSign) =
      fun r ↦ orderedIndexEquiv (modes r) := by
  funext r
  fin_cases r <;> rfl

/-- With canonical ordered frequencies, the exact free FPUT mismatch is the
same scalar mismatch recorded by the random-mass collision measure. -/
theorem quadraticPhaseMismatch_ordered_eq_orderedThreeWaveMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (leftSign rightSign : Fin 2) :
    quadraticPhaseMismatch (orderedPullbackFrequency m)
        (orderedIndexEquiv (modes 0))
        (orderedQuadraticPhaseTerm modes leftSign rightSign) =
      orderedThreeWaveMismatch m
        (quadraticCollisionSign
          (orderedQuadraticPhaseTerm modes leftSign rightSign)) modes := by
  rw [orderedPullbackFrequency_eq_modeFrequency]
  rw [quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch]
  rw [quadraticCollisionModes_orderedQuadraticPhaseTerm]
  exact (orderedThreeWaveMismatch_eq_phaseMismatch m
    (quadraticCollisionSign
      (orderedQuadraticPhaseTerm modes leftSign rightSign)) modes).symm

end

end ArchonPhysics.FreeFPUTCollisionMismatchBridge
